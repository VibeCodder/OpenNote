#!/usr/bin/env python3
"""
OpenNote - a Milanote-inspired mind-map / moodboard desktop application.

Built with PySide6 (native desktop UI was chosen over a browser/HTML front-end
because the app needs OS-level drag & drop of files, a resizable/movable
QGraphicsScene canvas, freehand drawing with pressure-less brushes, and
embedded video/gif playback - all of which are far more robust with a native
Qt Graphics View canvas than with a Python-driven web view).

Boards are saved as a single, self-contained .html file that:
  * can be opened and VIEWED (read-only, pan/zoom) in any web browser, and
  * can be opened and EDITED only from this application (the app reads the
    JSON board data that is embedded in the HTML file's <script> tag).

Run:
    python Opennote.py
"""

import sys
import os
import re
import copy
import math
import json
import base64
import atexit
import tempfile
import uuid
import time
import gc
import weakref
import types as _types

from PySide6.QtCore import (
    Qt, QRectF, QPointF, QPoint, QSize, QSizeF, QByteArray, QBuffer, QIODevice, QUrl, Signal, QTimer,
    QSettings,
)
from PySide6.QtGui import (
    QColor, QPen, QBrush, QPainter, QPainterPath, QPainterPathStroker, QPixmap, QImage, QFont,
    QFontMetrics,
    QMovie, QPalette, QKeySequence, QAction, QGuiApplication,
    QIcon, QActionGroup, QTextCursor, QIntValidator, QTextCharFormat, QTextDocument,
    QAbstractTextDocumentLayout,
)
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QGraphicsView, QGraphicsScene, QGraphicsObject,
    QGraphicsItem, QGraphicsTextItem, QGraphicsPathItem, QGraphicsRectItem, QGraphicsProxyWidget,
    QToolBar, QFileDialog, QColorDialog, QMessageBox, QSlider, QComboBox,
    QPushButton, QLabel, QWidget, QVBoxLayout, QHBoxLayout, QMenu, QToolButton,
    QFontComboBox, QInputDialog, QCompleter, QCheckBox,
    QDialog, QDialogButtonBox, QFormLayout, QSpinBox, QDoubleSpinBox, QGridLayout, QLineEdit,
    QSizePolicy, QTabWidget, QRadioButton, QButtonGroup,
)

try:
    from PySide6.QtOpenGLWidgets import QOpenGLWidget
    HAS_OPENGL = True
except Exception:
    HAS_OPENGL = False

try:
    from PySide6.QtMultimedia import QMediaPlayer, QAudioOutput
    # QGraphicsVideoItem (a real QGraphicsItem the scene paints directly)
    # is used instead of QVideoWidget for the actual video frames: a
    # QVideoWidget embedded through a QGraphicsProxyWidget reliably came
    # out solid black here even though playback (audio, position, timer)
    # was running fine - QVideoWidget owns its own native/GPU-composited
    # surface that the proxy widget's paint()-based compositing cannot
    # correctly capture. QGraphicsVideoItem has no such problem since it
    # renders frames straight into the scene like any other item.
    from PySide6.QtMultimediaWidgets import QGraphicsVideoItem
    HAS_MULTIMEDIA = True
except Exception:
    HAS_MULTIMEDIA = False


# --------------------------------------------------------------------------
# Constants & small helpers
# --------------------------------------------------------------------------

HANDLE_SIZE = 12
ARROW_Z_OFFSET = -1_000_000  # arrows default to a layer below every normal
                              # component (see MindMapScene.bring_to_front) -
                              # so a line tucks behind the boxes it connects
                              # instead of drawing over them
DRAWING_Z_OFFSET = 500_000  # freehand Draw strokes default to a layer above
                              # every normal component (see
                              # MindMapScene.bring_to_front) so a sketch stays
                              # visible on top no matter what gets added or
                              # brought to front afterward - the opposite of
                              # ARROW_Z_OFFSET's "always tucks behind"
ANCHOR_HIGHLIGHT_Z = 1_000_000  # the white outline shown over a component
                                  # while an arrow endpoint is dragged onto
                                  # it must stay visible above absolutely
                                  # everything, independent of ARROW_Z_OFFSET
ARROW_ANCHOR_MARKER_Z = ANCHOR_HIGHLIGHT_Z - 1  # green anchor-point rings for
                                  # a selected arrow's anchored endpoint(s) -
                                  # see MindMapScene.update_anchor_endpoint_markers.
                                  # Arrows themselves always paint below every
                                  # normal component (ARROW_Z_OFFSET), so an
                                  # anchored endpoint's marker - if drawn as
                                  # part of the arrow's own paint() - ends up
                                  # partly/fully hidden behind whatever it's
                                  # anchored to. This sits just under the drag
                                  # -time highlight but still above every
                                  # normal component, so the marker stays
                                  # visible on top of its target instead.
IMAGE_EXTS = {".png", ".jpg", ".jpeg", ".bmp", ".webp"}
GIF_EXTS = {".gif"}
VIDEO_EXTS = {".mp4", ".mov", ".avi", ".webm", ".mkv"}
RECENT_FILES_SETTINGS_KEY = "recentFiles"  # File > Recent, see MainWindow._add_recent_file
MAX_RECENT_FILES = 5

_TEMP_VIDEO_FILES = []


def _cleanup_temp_files():
    for p in _TEMP_VIDEO_FILES:
        try:
            if os.path.exists(p):
                os.remove(p)
        except Exception:
            pass


atexit.register(_cleanup_temp_files)


def new_id():
    return uuid.uuid4().hex[:12]


def sanitize_board_filename(name):
    """Turn a user-typed board name into a safe file basename (without
    extension) for a sibling board .html file in the project folder."""
    name = (name or "").strip()
    name = re.sub(r'[\\/:*?"<>|]', "_", name)
    name = re.sub(r"\s+", " ", name).strip()
    return name or "Board"


def normalize_link_url(url):
    """A URL typed without a scheme (e.g. "google.com" or "www.x.com")
    is a relative link as far as a browser is concerned, so clicking it
    in the exported HTML tries to open a local file next to the export
    and does nothing useful. Adding "https://" whenever no scheme is
    present (mailto:, tel:, http(s):, etc. are left untouched) is what
    makes those links actually navigate."""
    url = (url or "").strip()
    if not url:
        return ""
    if re.match(r"^[a-zA-Z][a-zA-Z0-9+.\-]*:", url):
        return url
    if url.startswith("//"):
        return "https:" + url
    return "https://" + url


def pixmap_to_base64(pixmap, fmt="PNG"):
    if pixmap is None or pixmap.isNull():
        return ""
    ba = QByteArray()
    buf = QBuffer(ba)
    buf.open(QIODevice.WriteOnly)
    pixmap.save(buf, fmt)
    buf.close()
    return base64.b64encode(ba.data()).decode("ascii")


def base64_to_pixmap(b64):
    pm = QPixmap()
    if b64:
        try:
            data = base64.b64decode(b64)
            pm.loadFromData(data)
        except Exception:
            pass
    return pm


class _MultiColorDialog(QDialog):
    """N-tab color picker - one tab per (label, start_color) pair, each
    hosting the exact same standard QColorDialog picker widget the rest
    of the app already uses for every other "Change Color" action, just
    embedded instead of shown standalone (QColorDialog.NoButtons hides
    its own OK/Cancel/pick-screen-color row - this dialog has one shared
    row for all tabs at the bottom instead). Powers both the classic
    two-tab Background/Top Strip picker and, in MainWindow.pick_color,
    a three-tab Text/Highlight/Top Strip picker when a selected text run
    happens to need both at once."""

    def __init__(self, parent, tabs, title="Pick color"):
        super().__init__(parent)
        self.setWindowTitle(title)
        layout = QVBoxLayout(self)
        tab_widget = QTabWidget()
        layout.addWidget(tab_widget)

        self._pickers = []
        for label, color in tabs:
            picker = QColorDialog(color, self)
            picker.setWindowFlags(Qt.Widget)
            picker.setOption(QColorDialog.NoButtons, True)
            # Without this, Qt tries to render the platform's *native*
            # color picker (the real OS dialog, e.g. Windows' own picker)
            # squeezed into a plain child widget here - which the native
            # dialog generally can't actually do, so the tab it's placed
            # in just renders empty instead of showing any color picker
            # at all. Forcing Qt's own cross-platform picker widget is
            # what makes embedding it inside a QTabWidget like this work.
            picker.setOption(QColorDialog.DontUseNativeDialog, True)
            tab_widget.addTab(picker, label)
            self._pickers.append(picker)

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        layout.addWidget(buttons)
        # Safety net alongside DontUseNativeDialog above: makes sure the
        # dialog opens at a sensible, usable size even if a picker widget
        # ever reports a degenerate size hint on some platform, instead
        # of the dialog collapsing down to barely visible.
        self.resize(520, 480)

    def selected_colors(self):
        return [p.currentColor() for p in self._pickers]


def open_multi_color_dialog(parent, tabs, title="Pick color"):
    """Show the N-tab picker above; `tabs` is a list of (label, start_color)
    pairs. Returns a list of chosen colors (same order as `tabs`) if
    accepted, or None if cancelled."""
    dlg = _MultiColorDialog(parent, tabs, title)
    if dlg.exec() == QDialog.Accepted:
        return dlg.selected_colors()
    return None


def open_bg_strip_color_dialog(parent, bg_start, strip_start, title="Pick component color", bg_label="Background",
                                strip_label="Top Strip"):
    """Show the two-tab picker above; returns (bg_color, strip_color) if
    accepted, or (None, None) if cancelled. bg_label names what the first
    tab actually controls - "Background" for a real fill (Text Note,
    Board Card), "Border" for Image/GIF/Video (see TopStripMixin.
    COLOR_TAB_LABEL). strip_label names the second tab - "Top Strip" for
    components, or "Highlight" when reused for text highlight color (see
    MainWindow.pick_color)."""
    result = open_multi_color_dialog(parent, [(bg_label, bg_start), (strip_label, strip_start)], title)
    if result is None:
        return None, None
    return result[0], result[1]


# File extension -> MIME type for board-link thumbnails (raster images
# plus SVG). Anything else is rejected by load_thumb_file() below.
THUMB_EXTS = {
    ".png": "image/png",
    ".jpg": "image/jpeg",
    ".jpeg": "image/jpeg",
    ".bmp": "image/bmp",
    ".webp": "image/webp",
    ".gif": "image/gif",
    ".svg": "image/svg+xml",
}


def load_thumb_file(path):
    """Read an image or SVG file picked by the user for a board-link
    thumbnail/icon, returning (mime, base64_data) ready to be embedded
    as a `data:` URI - both in the app's own rendering (see
    thumb_to_pixmap) and in the exported HTML (BoardLinkItem.to_html),
    exactly like every other embedded image in the app. Returns
    (None, None) if the file's extension isn't a recognised image/SVG
    type or it couldn't be read.
    """
    ext = os.path.splitext(path)[1].lower()
    mime = THUMB_EXTS.get(ext)
    if not mime:
        return None, None
    try:
        with open(path, "rb") as f:
            raw = f.read()
    except Exception:
        return None, None
    return mime, base64.b64encode(raw).decode("ascii")


def thumb_to_pixmap(mime, b64_data, size=96):
    """Decode a board-link thumbnail (see load_thumb_file) into a QPixmap
    for on-canvas / dialog-preview rendering. Raster formats decode
    directly through QPixmap; SVG is rasterized through QSvgRenderer
    (falling back to QPixmap's own loader, which also understands SVG
    when Qt's svg imageformat plugin is installed) so an .svg thumbnail
    still shows up even without the QtSvg Python module available.
    """
    if not b64_data:
        return None
    try:
        raw = base64.b64decode(b64_data)
    except Exception:
        return None
    if mime == "image/svg+xml":
        try:
            from PySide6.QtSvg import QSvgRenderer
            renderer = QSvgRenderer(QByteArray(raw))
            if renderer.isValid():
                default_size = renderer.defaultSize()
                if default_size.width() > 0 and default_size.height() > 0:
                    scale = min(size / default_size.width(), size / default_size.height())
                    tw = max(1, int(default_size.width() * scale))
                    th = max(1, int(default_size.height() * scale))
                else:
                    tw = th = size
                pm = QPixmap(size, size)
                pm.fill(Qt.transparent)
                painter = QPainter(pm)
                target = QRectF((size - tw) / 2.0, (size - th) / 2.0, tw, th)
                renderer.render(painter, target)
                painter.end()
                return pm
        except Exception:
            pass
        # Fallback: Qt's own image-format plugin can rasterize SVG too,
        # when it's installed alongside QtSvg.
        pm = QPixmap()
        if pm.loadFromData(raw) and not pm.isNull():
            return pm
        return None
    pm = QPixmap()
    if pm.loadFromData(raw) and not pm.isNull():
        return pm
    return None


def color_to_css(color_str):
    """Convert an internal color string to a value that is valid CSS/SVG.

    Internally, colors that carry transparency (e.g. highlighter strokes)
    are stored using Qt's QColor.name(QColor.HexArgb) format, which is
    "#AARRGGBB" (alpha FIRST). That is not a format CSS or SVG understands
    - browsers either ignore it or misread the alpha byte as part of the
    red channel, which is why colors exported to HTML looked wrong. This
    always returns a browser-safe "rgba(r,g,b,a)" (or plain "#RRGGBB" when
    there is no transparency) string."""
    if not color_str:
        return "#ffffff"
    s = color_str.strip()
    if s.startswith("#") and len(s) == 9:
        a = int(s[1:3], 16)
        r = int(s[3:5], 16)
        g = int(s[5:7], 16)
        b = int(s[7:9], 16)
        if a >= 255:
            return f"#{r:02x}{g:02x}{b:02x}"
        return f"rgba({r},{g},{b},{a / 255.0:.3f})"
    return s


# --------------------------------------------------------------------------
# Small, self-contained vector icons for the toolbar (drawn with QPainter so
# the app stays a single .py file with no external icon assets to ship).
# --------------------------------------------------------------------------

def _make_toolbar_icon(kind, size=20, color="#e8e8e8"):
    pm = QPixmap(size, size)
    pm.fill(Qt.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.Antialiasing)
    pen = QPen(QColor(color), 1.6)
    pen.setJoinStyle(Qt.RoundJoin)
    pen.setCapStyle(Qt.RoundCap)
    p.setPen(pen)
    p.setBrush(Qt.NoBrush)
    m = 2.6

    if kind == "text":
        p.drawRoundedRect(QRectF(m, m, size - 2 * m, size - 2 * m), 2, 2)
        for frac in (0.38, 0.58, 0.78):
            y = m + 2 + (size - 2 * m - 4) * frac
            p.drawLine(QPointF(m + 3, y), QPointF(size - m - 3, y))
    elif kind == "plaintext":
        # Deliberately no surrounding frame, to visually distinguish this
        # "just text" component from the framed Text Note ("text") icon.
        for frac, inset in ((0.28, 0), (0.5, 0), (0.72, size * 0.32)):
            y = m + (size - 2 * m) * frac
            p.drawLine(QPointF(m, y), QPointF(size - m - inset, y))
    elif kind == "board":
        p.drawRoundedRect(QRectF(m, m, size - 2 * m, size - 2 * m), 2, 2)
        p.drawLine(QPointF(m, m + 5.5), QPointF(size - m, m + 5.5))
        p.drawLine(QPointF(m + 3, m + 10), QPointF(size - m - 3, m + 10))
        p.drawLine(QPointF(m + 3, m + 14), QPointF(size - m - 7, m + 14))
    elif kind == "board_link":
        p.drawRoundedRect(QRectF(m, m, size - 2 * m, size - 2 * m), 2, 2)
        p.drawLine(QPointF(m + 3, m + 5.5), QPointF(size - m - 3, m + 5.5))
        cx0, cy0 = size * 0.36, size * 0.66
        cx1, cy1 = size * 0.72, size * 0.66
        p.drawLine(QPointF(cx0, cy0), QPointF(cx1, cy1))
        p.drawLine(QPointF(cx1, cy1), QPointF(cx1 - 4, cy1 - 4))
        p.drawLine(QPointF(cx1, cy1), QPointF(cx1 - 4, cy1 + 1))
    elif kind == "table":
        p.drawRoundedRect(QRectF(m, m, size - 2 * m, size - 2 * m), 2, 2)
        header_y = m + (size - 2 * m) * 0.32
        p.drawLine(QPointF(m, header_y), QPointF(size - m, header_y))
        mid_x = size / 2.0
        p.drawLine(QPointF(mid_x, header_y), QPointF(mid_x, size - m))
        row_y = m + (size - 2 * m) * 0.66
        p.drawLine(QPointF(m, row_y), QPointF(size - m, row_y))
    elif kind == "image":
        p.drawRoundedRect(QRectF(m, m, size - 2 * m, size - 2 * m), 2, 2)
        p.setBrush(QColor(color))
        p.setPen(Qt.NoPen)
        p.drawEllipse(QPointF(m + 5, m + 5.5), 1.7, 1.7)
        p.setBrush(Qt.NoBrush)
        p.setPen(pen)
        path = QPainterPath()
        path.moveTo(m + 2, size - m - 2)
        path.lineTo(m + 7.5, m + 9.5)
        path.lineTo(m + 10.5, size - m - 5)
        path.lineTo(m + 13.5, m + 7.5)
        path.lineTo(size - m - 2, size - m - 2)
        p.drawPath(path)
    elif kind == "gif":
        p.drawRoundedRect(QRectF(m, m, size - 2 * m, size - 2 * m), 2, 2)
        f = QFont("Arial", max(6, int(size * 0.28)), QFont.Bold)
        p.setFont(f)
        p.drawText(QRectF(m, m, size - 2 * m, size - 2 * m), Qt.AlignCenter, "GIF")
    elif kind == "video":
        p.drawRoundedRect(QRectF(m, m, size - 2 * m, size - 2 * m), 2, 2)
        p.setBrush(QColor(color))
        p.setPen(Qt.NoPen)
        cx, cy = size / 2.0, size / 2.0
        tri = QPainterPath()
        tri.moveTo(cx - 2.6, cy - 4.2)
        tri.lineTo(cx - 2.6, cy + 4.2)
        tri.lineTo(cx + 4.2, cy)
        tri.closeSubpath()
        p.drawPath(tri)
    elif kind == "draw":
        # A recognizable pencil: graphite tip, wooden body, metal ferrule
        # and an eraser cap, laid out diagonally (writing angle).
        p.setPen(Qt.NoPen)
        p.save()
        p.translate(size / 2, size / 2)
        p.rotate(-45)
        length = size - 5
        body_w = 3.4
        tip_len = 5.0
        eraser_len = 3.0
        ferrule_len = 2.0
        x0, x1 = -length / 2, length / 2

        tip = QPainterPath()
        tip.moveTo(x0, 0)
        tip.lineTo(x0 + tip_len, -body_w / 2)
        tip.lineTo(x0 + tip_len, body_w / 2)
        tip.closeSubpath()
        p.setBrush(QColor(color))
        p.drawPath(tip)

        body_x1 = x1 - eraser_len - ferrule_len
        p.drawRect(QRectF(x0 + tip_len, -body_w / 2, body_x1 - (x0 + tip_len), body_w))

        p.setBrush(QColor(color).lighter(150))
        p.drawRect(QRectF(body_x1, -body_w / 2 - 0.4, ferrule_len, body_w + 0.8))

        p.setBrush(QColor(color))
        p.drawRoundedRect(QRectF(x1 - eraser_len, -body_w / 2 - 0.4, eraser_len, body_w + 0.8), 1, 1)
        p.restore()
    elif kind == "select":
        p.setBrush(QColor(color))
        p.setPen(QPen(QColor(color), 1))
        arrow = QPainterPath()
        arrow.moveTo(m + 2, m + 1)
        arrow.lineTo(m + 2, size - m - 1)
        arrow.lineTo(m + 7, size - m - 5.5)
        arrow.lineTo(m + 9.5, size - m - 1)
        arrow.lineTo(m + 11.5, size - m - 2.2)
        arrow.lineTo(m + 8.3, size - m - 6.5)
        arrow.lineTo(size - m - 1.5, size - m - 8)
        arrow.closeSubpath()
        p.drawPath(arrow)
    elif kind == "duplicate":
        p.drawRoundedRect(QRectF(m + 3, m + 1, size - 2 * m - 3, size - 2 * m - 3), 2, 2)
        p.drawRoundedRect(QRectF(m, m + 4, size - 2 * m - 3, size - 2 * m - 3), 2, 2)
    elif kind == "delete":
        p.drawLine(QPointF(m + 6, m), QPointF(size - m - 6, m))
        p.drawLine(QPointF(m + 1, m + 3.5), QPointF(size - m - 1, m + 3.5))
        p.drawRoundedRect(QRectF(m + 3, m + 3.5, size - 2 * m - 4, size - m - 4.5), 1.5, 1.5)
        for frac in (0.32, 0.5, 0.68):
            x = m + 3 + (size - 2 * m - 4) * frac
            p.drawLine(QPointF(x, m + 6.5), QPointF(x, size - m - 5.5))
    elif kind == "arrow":
        tail = QPointF(m + 1.5, size - m - 1.5)
        tip = QPointF(size - m - 2, m + 2)
        p.drawLine(tail, tip)
        p.setBrush(QColor(color))
        p.setPen(Qt.NoPen)
        head = QPainterPath()
        head.moveTo(tip)
        head.lineTo(tip.x() - 6.5, tip.y() + 1.5)
        head.lineTo(tip.x() - 1.5, tip.y() + 6.5)
        head.closeSubpath()
        p.drawPath(head)
    elif kind == "color":
        p.setPen(Qt.NoPen)
        p.setBrush(QColor("#ff6b6b"))
        p.drawEllipse(QPointF(size * 0.35, size * 0.4), 4.2, 4.2)
        p.setBrush(QColor("#4c8bf5"))
        p.drawEllipse(QPointF(size * 0.62, size * 0.4), 4.2, 4.2)
        p.setBrush(QColor("#ffd93d"))
        p.drawEllipse(QPointF(size * 0.5, size * 0.65), 4.2, 4.2)

    p.end()
    return QIcon(pm)


# --------------------------------------------------------------------------
# Editable text item (used for note text and board card titles)
# --------------------------------------------------------------------------

CHECK_UNCHECKED = "\u2610"  # unicode empty checkbox glyph
CHECK_CHECKED = "\u2611"    # unicode checked checkbox glyph
BULLET_CHAR = "\u2022"      # unicode bullet dot


def _apply_text_font(item, family=None, bold=None, italic=None, underline=None, point_size=None,
                      editing_item=None):
    """Shared helper used by TextNoteItem/PlainTextItem/TableItem (both
    directly and from the toolbar's font/B/I/U controls) to mutate a text
    component's font. Formatting here applies to the whole text item
    rather than a per-character selection - these are simple sticky-note
    style text components (stored/exported as plain text), not a
    rich-text editor.

    Most components expose a single `.text_item`; TableItem instead
    exposes `font_targets(editing_item)`, returning either just the one
    cell currently being edited (if `editing_item` belongs to it) or
    every cell in the table (so a whole-table selection restyles every
    cell at once, the same way this restyles a whole Text Note).

    Selection-aware: while `editing_item` is one of the returned targets
    AND that target currently has an actual text selection (a
    highlighted range, not just a blinking caret), the change is applied
    to just that selected run of characters - real per-character rich
    text, like any ordinary text editor's toolbar. With no selection
    (including whenever nothing at all is being edited, i.e. a whole
    component is simply selected on the canvas) the same change is
    instead applied uniformly across the entire text field, matching the
    original whole-item-only behavior."""
    targets = item.font_targets(editing_item) if hasattr(item, "font_targets") else [item.text_item]
    for t in targets:
        has_sel = (t is editing_item) and t.textCursor().hasSelection()

        # Only mutate the item's whole-field default font when the change
        # is meant to apply to the whole field. QGraphicsTextItem.setFont()
        # rewrites the document's ambient/default char format - if called
        # even while there's a real selection, it silently changes what
        # format *new* text picks up anywhere in the field, which is how
        # "bold" used to leak onto text the user never selected.
        if not has_sel:
            f = t.font()
            if family is not None:
                f.setFamily(family)
            if bold is not None:
                f.setBold(bold)
            if italic is not None:
                f.setItalic(italic)
            if underline is not None:
                f.setUnderline(underline)
            if point_size is not None:
                f.setPointSizeF(max(1.0, float(point_size)))
            t.setFont(f)

        _apply_run_format(t, has_sel, family=family, bold=bold, italic=italic,
                           underline=underline, point_size=point_size)

    # setFont() does not emit the document's contentsChanged signal (only
    # actual text edits do), so a TableItem never hears about a font/size
    # change through _on_cell_text_changed and its row heights go stale -
    # the new, possibly taller text then overflows the old row bounds.
    # Force a relayout here whenever the target exposes one (TableItem,
    # or a MediaCardMixin item's title/description bars).
    if hasattr(item, "_layout_cells"):
        item._layout_cells()
        item.update()
    if hasattr(item, "_on_title_desc_text_changed"):
        item._on_title_desc_text_changed()
        item.update()
    if hasattr(item, "_on_label_text_changed"):
        item._on_label_text_changed()
        item.update()
    if hasattr(item, "_on_subitem_text_font_changed"):
        item._on_subitem_text_font_changed()
        item.update()
    if isinstance(item, TextNoteItem):
        item._on_text_changed()
        item.update()


_UNSET = object()  # sentinel: "leave this property alone" vs. an explicit None


def _apply_text_alignment(item, alignment, editing_item=None):
    """Set paragraph alignment (Qt.AlignLeft / Qt.AlignHCenter / Qt.AlignRight)
    for a text component - the counterpart to _apply_text_font above, but
    for a block-level property instead of a character-level one.

    Unlike Bold/Italic/Underline/color, "no selection" here must NOT
    mean "whole field" while a specific paragraph actually has the live
    cursor in it - alignment is what a real cursor position (not just a
    highlighted range) already scopes to in any ordinary rich text
    editor: an unselected caret still restyles its own paragraph, not
    every other paragraph in the field along with it. So while `t` is
    the exact field actually being edited, this reuses its own live
    QTextCursor as-is and lets Qt's mergeBlockFormat() apply the
    alignment to whichever block(s) that cursor is genuinely in or
    touching right now - the current block alone with no selection, or
    every block a real selection spans. Only when `t` ISN'T being
    edited at all (including whenever nothing at all is being edited,
    i.e. a whole component is simply selected on the canvas) does it
    fall back to the whole field, matching the original whole-item-only
    behavior.

    setHtml()/toHtml() already round-trip block alignment on their own
    (it's just a per-<p> inline style to Qt), so this needs no extra
    serialization work anywhere components are saved/loaded."""
    targets = item.font_targets(editing_item) if hasattr(item, "font_targets") else [item.text_item]
    for t in targets:
        if t is editing_item:
            cur = t.textCursor()
        else:
            cur = QTextCursor(t.document())
            cur.select(QTextCursor.Document)
        block_fmt = cur.blockFormat()
        block_fmt.setAlignment(alignment)
        cur.mergeBlockFormat(block_fmt)

    # Same relayout hooks as _apply_text_font - a plain mergeBlockFormat()
    # doesn't itself emit the document's contentsChanged signal, so
    # anything that caches row/bar heights off the text needs nudging
    # by hand or it'll go stale exactly like a font/size change would.
    if hasattr(item, "_layout_cells"):
        item._layout_cells()
        item.update()
    if hasattr(item, "_on_title_desc_text_changed"):
        item._on_title_desc_text_changed()
        item.update()
    if hasattr(item, "_on_label_text_changed"):
        item._on_label_text_changed()
        item.update()
    if hasattr(item, "_on_subitem_text_font_changed"):
        item._on_subitem_text_font_changed()
        item.update()
    if isinstance(item, TextNoteItem):
        item._on_text_changed()
        item.update()


def _apply_run_format(text_item, has_selection, family=None, bold=None, italic=None,
                       underline=None, point_size=None, foreground=_UNSET, background=_UNSET,
                       anchor_url=_UNSET):
    """Low-level formatting primitive shared by every toolbar text control
    (Font family / Bold / Italic / Underline / Size / Color / Highlight /
    Link): merges a QTextCharFormat built from whichever of these are
    given into either `text_item`'s current selection (has_selection=True
    - real per-character rich text, exactly like any ordinary editor's
    toolbar) or, with has_selection=False, a cursor spanning its entire
    document (so the change reads as "the whole text field changed") -
    this also overwrites any earlier per-character formatting already in
    that field, so "no selection = whole field" stays literally true even
    after part of it was restyled a different way a moment ago.

    `foreground` and `background` follow the same "unset vs explicit"
    convention as `anchor_url`: leave the argument out entirely to not
    touch that property, pass a color (name/QColor) to set it, or pass
    "" / None to explicitly clear it back to the item's own default."""
    cur = text_item.textCursor() if has_selection else QTextCursor(text_item.document())
    if not has_selection:
        cur.select(QTextCursor.Document)
    if not cur.hasSelection():
        return
    fmt = QTextCharFormat()
    if family is not None:
        fmt.setFontFamily(family)
    if bold is not None:
        fmt.setFontWeight(QFont.Bold if bold else QFont.Normal)
    if italic is not None:
        fmt.setFontItalic(italic)
    if point_size is not None:
        fmt.setFontPointSize(max(1.0, float(point_size)))
    if foreground is not _UNSET:
        if foreground:
            fmt.setForeground(QColor(foreground))
        else:
            # NOTE: clearForeground() would *remove* the property from
            # this patch format instead of setting it - and
            # mergeCharFormat() below only copies over properties that
            # are actually present in the patch, so a removed property
            # leaves whatever the destination already had untouched.
            # An explicit empty QBrush (style NoBrush) *is* a real,
            # merge-visible property, and NoBrush is exactly what Qt
            # treats as "no override, fall back to the item's default
            # color" (see editing_item.defaultTextColor() usage in
            # _refresh_text_format_buttons) - so this is what actually
            # clears a previously set color.
            fmt.setForeground(QBrush())
    if background is not _UNSET:
        if background:
            fmt.setBackground(QBrush(QColor(background)))
        else:
            # Same reasoning as foreground above: clearBackground() is a
            # no-op through mergeCharFormat, an explicit NoBrush is not.
            fmt.setBackground(QBrush())
    if anchor_url is not _UNSET:
        if anchor_url:
            fmt.setAnchor(True)
            fmt.setAnchorHref(anchor_url)
        else:
            fmt.setAnchor(False)
            fmt.setAnchorHref("")
    # Underline is intentionally decoupled from the anchor branch above
    # (rather than an `elif`) so an explicit underline=False can still
    # clear the link's own auto-underline when a link is being removed
    # (see MainWindow.on_hyperlink_clicked) - previously the two were
    # mutually exclusive, which silently dropped any underline=False
    # passed alongside anchor_url and left removed links visually
    # underlined forever after.
    if underline is not None:
        fmt.setFontUnderline(underline)
    elif anchor_url is not _UNSET and anchor_url:
        # A newly-created hyperlink implies its familiar underlined look
        # (same as when a whole item first becomes a link), unless an
        # explicit underline value was already given above.
        fmt.setFontUnderline(True)
    cur.mergeCharFormat(fmt)


def _document_has_anchor(document):
    """Whether any run of `document` already carries its own per-character
    hyperlink formatting (set via _apply_run_format) - used by to_html()
    to decide whether an item-level `link_url` (the older, whole-field-only
    way a link could be stored) still needs to be applied as an outer
    wrapper, or whether the rich text itself already accounts for it."""
    block = document.begin()
    while block.isValid():
        it = block.begin()
        while not it.atEnd():
            frag = it.fragment()
            if frag.isValid() and frag.charFormat().isAnchor():
                return True
            it += 1
        block = block.next()
    return False


def _text_run_to_html(frag_text, fmt, base_family, base_size):
    """Render one same-formatted run of characters (a QTextFragment) as
    a <span> (or <a>, if it's a hyperlink run) carrying exactly its own
    font/color/bold/italic/underline - the building block that lets the
    exported HTML mirror per-character rich text instead of one style
    for an entire field."""
    text = frag_text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    if not text:
        return ""
    f = fmt.font()
    style_bits = []
    family = f.family() or base_family
    style_bits.append(f"font-family:'{family}',sans-serif")
    size = f.pointSizeF()
    if size <= 0:
        size = base_size
    style_bits.append(f"font-size:{size:.1f}pt")
    fg = fmt.foreground()
    if fg.style() != Qt.NoBrush:
        style_bits.append(f"color:{fg.color().name()}")
    bg = fmt.background()
    if bg.style() != Qt.NoBrush:
        style_bits.append(f"background-color:{bg.color().name()}")
    if f.bold() or f.weight() > QFont.Normal:
        style_bits.append("font-weight:bold")
    if f.italic():
        style_bits.append("font-style:italic")
    is_link = fmt.isAnchor() and bool(fmt.anchorHref())
    if f.underline() or is_link:
        style_bits.append("text-decoration:underline")
    style = ";".join(style_bits)
    if is_link:
        safe_url = fmt.anchorHref().replace('"', "&quot;")
        return f'<a href="{safe_url}" target="_blank" rel="noopener noreferrer" style="{style}">{text}</a>'
    return f'<span style="{style}">{text}</span>'


def _block_align_css(block_format):
    """Map a QTextBlockFormat's alignment to a CSS text-align value -
    shared by _qtextdocument_to_web_html below. Qt.AlignLeft (and any
    default/unset block, which reads back as Qt.AlignLeft) needs no
    special case: "left" is also the CSS default, but it's still spelled
    out explicitly here rather than omitted, so exported alignment is
    never silently at the mercy of some other CSS rule's default."""
    align = block_format.alignment()
    if align & Qt.AlignHCenter:
        return "center"
    if align & Qt.AlignRight:
        return "right"
    if align & Qt.AlignJustify:
        return "justify"
    return "left"


def _qtextdocument_to_web_html(document, base_family="Segoe UI", base_size=11.0):
    """Render a QTextDocument's actual rich, per-character formatting
    (one <span>/<a> per differently-formatted run: bold, italic,
    underline, color, font, hyperlink, ...) as portable HTML for the
    exported board file, so a browser shows exactly what the app shows -
    formatting selection-by-selection, not just one style per field.
    Each paragraph becomes its own margin-free <div> (rather than just
    joining blocks with <br>) so each one can carry its own text-align -
    alignment is a block-level property in Qt's rich text model, unlike
    the character-level formatting the spans inside already handle."""
    parts = []
    block = document.begin()
    while block.isValid():
        run_parts = []
        it = block.begin()
        while not it.atEnd():
            frag = it.fragment()
            if frag.isValid() and frag.length() > 0:
                run_parts.append(_text_run_to_html(frag.text(), frag.charFormat(), base_family, base_size))
            it += 1
        align = _block_align_css(block.blockFormat())
        content = "".join(run_parts) or "&nbsp;"
        parts.append(f'<div style="margin:0;padding:0;text-align:{align}">{content}</div>')
        block = block.next()
    return "".join(parts)


def _subitem_top_strip_html(item):
    """Board Card subitems (image/gif/video/text) can each have their own
    Top Strip, same as the standalone components they came from - but
    they only exist as plain dict data inside the card (no live
    TopStripMixin instance), so BoardCardItem.to_html() needs its own
    tiny renderer instead of calling TopStripMixin._top_strip_html()."""
    if not item.get("top_strip_enabled"):
        return ""
    color = item.get("top_strip_color") or TopStripMixin.DEFAULT_STRIP_COLOR
    return (f'<div style="position:absolute;left:0;top:0;right:0;'
            f'height:{TopStripMixin.TOP_STRIP_H}px;background:{color};"></div>')


def _rich_html_from_doc_html(doc_html, base_family="Segoe UI", base_size=11.0):
    """Reconstruct a throwaway QTextDocument from Qt's own toHtml() output
    (as stashed in a *_html field by serialize()/subitem editing) and
    re-render it through _qtextdocument_to_web_html() to get portable,
    per-run web HTML - including any highlight/color/bold/italic/underline
    runs - out of text that only exists as saved dict/JSON data rather
    than a live QGraphicsTextItem (Board Card subitems - see
    BoardCardItem.to_html()). Returns None if there's nothing to render.
    """
    if not doc_html:
        return None
    doc = QTextDocument()
    doc.setHtml(doc_html)
    if not doc.toPlainText().strip():
        return None
    return _qtextdocument_to_web_html(doc, base_family=base_family, base_size=base_size)


def _force_font_family_in_html(doc_html, family):
    """Rewrite every run of a saved *_html string (Qt's own toHtml()
    output, as stashed by serialize()/subitem editing) to use `family`,
    overriding whatever specific font each run already carries.

    This is what "Apply Font to All Components" actually needs and what
    replace_all_font_families alone doesn't provide: toHtml() always
    bakes an explicit font-family into every run it writes (even ones
    that were never deliberately given a special font), so
    QTextCharFormat.font().family() never reads back empty/"inherited" -
    swapping only the item's separate "font_family" summary field (used
    solely to build a fresh default QFont at load time) has no visible
    effect on text that already has real content, since setHtml() below
    always wins over that summary field once text exists. Forcing every
    run's family here, then re-serializing, is what makes the new font
    actually show up - in the app AND in the exported HTML, since the
    browser-facing export (_qtextdocument_to_web_html) reads directly
    from these same runs.

    Returns the rewritten HTML, or the original value unchanged if it's
    empty/falsy (nothing to rewrite)."""
    if not doc_html:
        return doc_html
    doc = QTextDocument()
    doc.setHtml(doc_html)
    doc.setDefaultFont(QFont(family))
    cur = QTextCursor(doc)
    cur.select(QTextCursor.Document)
    fmt = QTextCharFormat()
    fmt.setFontFamily(family)
    cur.mergeCharFormat(fmt)
    return doc.toHtml()


def _paint_rich_doc(painter, doc, rect, default_color):
    """Paint a QTextDocument (built from a subitem's stored *_html, or
    plain text as a fallback) at `rect`, honoring per-run background
    (highlight) the same way the live in-place editors do - plain
    QPainter.drawText() has no concept of that, which is why a subitem's
    highlight used to only ever show while actively being edited and
    vanish the instant editing ended (see BoardCardItem.paint()). This
    drives the same QAbstractTextDocumentLayout a QGraphicsTextItem uses
    internally, just directly, since these subitems don't have a
    permanent QGraphicsTextItem of their own."""
    painter.save()
    painter.setClipRect(rect)
    painter.translate(rect.topLeft())
    ctx = QAbstractTextDocumentLayout.PaintContext()
    ctx.palette.setColor(QPalette.Text, default_color)
    ctx.clip = QRectF(0, 0, rect.width(), rect.height())
    doc.documentLayout().draw(painter, ctx)
    painter.restore()


def _representative_font(item, editing_item=None):
    """The font shown in the toolbar (combo/B/I/U/size) for the current
    selection - the font of whichever single cell is being edited, or of
    the first cell/text item otherwise."""
    if hasattr(item, "font_targets"):
        targets = item.font_targets(editing_item)
        return targets[0].font() if targets else QFont("Segoe UI", 10)
    return item.text_item.font()


def _representative_alignment(item, editing_item=None):
    """The alignment shown in the toolbar's Align dropdown for the
    current selection - the block alignment at the live cursor (if
    that's one of the returned targets), or of the first paragraph of
    the first cell/text item otherwise. Mirrors _representative_font's
    editing_item handling above, just reading blockFormat() instead of
    the character format."""
    if hasattr(item, "font_targets"):
        targets = item.font_targets(editing_item)
        target = targets[0] if targets else None
    else:
        target = item.text_item
    if target is None:
        return Qt.AlignLeft
    if target is editing_item:
        return target.textCursor().blockFormat().alignment()
    return target.document().firstBlock().blockFormat().alignment()


def _font_to_dict(f):
    return {
        "font_family": f.family(),
        "font_size": f.pointSizeF(),
        "bold": f.bold(),
        "italic": f.italic(),
        "underline": f.underline(),
    }


def _font_from_dict(d, base_family="Segoe UI", base_size=10.0, base_bold=False):
    d = d or {}
    f = QFont(d.get("font_family") or base_family)
    f.setPointSizeF(d.get("font_size") or base_size)
    f.setBold(d.get("bold", base_bold))
    f.setItalic(d.get("italic", False))
    f.setUnderline(d.get("underline", False))
    return f


# --------------------------------------------------------------------------
# App preferences (Settings > Preferences) - persisted via QSettings so they
# survive between runs. Only two things read/write these: PreferencesDialog
# (the editor) and MainWindow's add_*/create_item_from_file component
# creation methods (the consumer, applying them as the defaults a brand new
# component starts out with - see _apply_new_component_prefs).
# --------------------------------------------------------------------------

PREF_ALIGN_OPTIONS = [("left", "Left"), ("center", "Center"), ("right", "Right")]
PREF_ALIGN_TO_QT = {"left": Qt.AlignLeft, "center": Qt.AlignHCenter, "right": Qt.AlignRight}

# Arrow endpoint snapping method - governs how an anchored arrow endpoint
# behaves once its target component moves (see ArrowItem.refresh_anchors /
# _effective_snap_method):
#   "orbit"    - (default, previous-and-only behaviour) the endpoint keeps
#                re-picking whichever border point on the target currently
#                faces the arrow's other end, so it slides all the way
#                around the target as things move - see _border_point.
#   "absolute" - the endpoint stays glued to the exact point on the target
#                it was originally dropped on ("punkt zaczepienia") and
#                only tracks the target's own move/resize, never re-orbits
#                to face the other end.
# The app-wide default lives in Preferences; any individual component can
# override it for itself via its own context menu's "Arrow Snapping"
# submenu (see BaseComponentItem.arrow_snap_method / _add_arrow_snap_menu).
ARROW_SNAP_METHODS = ["orbit", "absolute"]
ARROW_SNAP_METHOD_OPTIONS = [
    ("orbit", "Snap Around All Sides (Orbit)"),
    ("absolute", "Snap To Fixed Anchor Point (Absolute)"),
]

DEFAULT_PREFS = {
    "default_show_title": True,
    "default_show_description": True,
    "default_title_alignment": "left",   # one of PREF_ALIGN_OPTIONS
    "default_font_family": "Segoe UI",
    "default_title_font_size": 12.0,
    "default_description_font_size": 9.0,
    "default_arrow_size": 4,
    # -- background dot-grid rendering (see MindMapScene.drawBackground) --
    # The grid-spacing-doubling trick already keeps the dot COUNT roughly
    # constant at any zoom level, but building + drawing even that capped
    # set of points still runs on every single repaint (i.e. continuously
    # while panning/zooming). "optimize_grid_rendering" lets that fixed
    # per-frame cost be skipped entirely once the view is zoomed out past
    # grid_disable_zoom_percent, since the dots are barely visible at
    # extreme zoom-out anyway.
    "optimize_grid_rendering": True,
    "grid_disable_zoom_percent": 15.0,  # skip the dot grid once zoom <= this %
    "default_arrow_snap_method": "orbit",  # one of ARROW_SNAP_METHODS
}


def load_app_preferences():
    s = QSettings("OpenNote", "OpenNote")
    prefs = dict(DEFAULT_PREFS)
    s.beginGroup("preferences")
    prefs["default_show_title"] = _qsettings_bool(s, "default_show_title", DEFAULT_PREFS["default_show_title"])
    prefs["default_show_description"] = _qsettings_bool(
        s, "default_show_description", DEFAULT_PREFS["default_show_description"])
    align = s.value("default_title_alignment", DEFAULT_PREFS["default_title_alignment"])
    prefs["default_title_alignment"] = align if align in PREF_ALIGN_TO_QT else "left"
    fam = s.value("default_font_family", DEFAULT_PREFS["default_font_family"])
    prefs["default_font_family"] = fam or DEFAULT_PREFS["default_font_family"]
    try:
        prefs["default_title_font_size"] = float(
            s.value("default_title_font_size", DEFAULT_PREFS["default_title_font_size"]))
    except (TypeError, ValueError):
        prefs["default_title_font_size"] = DEFAULT_PREFS["default_title_font_size"]
    try:
        prefs["default_description_font_size"] = float(
            s.value("default_description_font_size", DEFAULT_PREFS["default_description_font_size"]))
    except (TypeError, ValueError):
        prefs["default_description_font_size"] = DEFAULT_PREFS["default_description_font_size"]
    try:
        prefs["default_arrow_size"] = int(
            s.value("default_arrow_size", DEFAULT_PREFS["default_arrow_size"]))
    except (TypeError, ValueError):
        prefs["default_arrow_size"] = DEFAULT_PREFS["default_arrow_size"]
    prefs["optimize_grid_rendering"] = _qsettings_bool(
        s, "optimize_grid_rendering", DEFAULT_PREFS["optimize_grid_rendering"])
    try:
        prefs["grid_disable_zoom_percent"] = float(
            s.value("grid_disable_zoom_percent", DEFAULT_PREFS["grid_disable_zoom_percent"]))
    except (TypeError, ValueError):
        prefs["grid_disable_zoom_percent"] = DEFAULT_PREFS["grid_disable_zoom_percent"]
    snap_method = s.value("default_arrow_snap_method", DEFAULT_PREFS["default_arrow_snap_method"])
    prefs["default_arrow_snap_method"] = snap_method if snap_method in ARROW_SNAP_METHODS else "orbit"
    s.endGroup()
    return prefs


def save_app_preferences(prefs):
    s = QSettings("OpenNote", "OpenNote")
    s.beginGroup("preferences")
    s.setValue("default_show_title", bool(prefs.get("default_show_title", True)))
    s.setValue("default_show_description", bool(prefs.get("default_show_description", True)))
    s.setValue("default_title_alignment", prefs.get("default_title_alignment", "left"))
    s.setValue("default_font_family", prefs.get("default_font_family", "Segoe UI"))
    s.setValue("default_title_font_size", float(prefs.get("default_title_font_size", 12.0)))
    s.setValue("default_description_font_size", float(prefs.get("default_description_font_size", 9.0)))
    s.setValue("default_arrow_size", int(prefs.get("default_arrow_size", 4)))
    s.setValue("optimize_grid_rendering", bool(prefs.get("optimize_grid_rendering", True)))
    s.setValue("grid_disable_zoom_percent", float(prefs.get("grid_disable_zoom_percent", 15.0)))
    s.setValue("default_arrow_snap_method", prefs.get("default_arrow_snap_method", "orbit"))
    s.endGroup()


def _qsettings_bool(settings, key, default):
    # QSettings round-trips bools as the strings "true"/"false" on some
    # platforms/backends instead of real bool objects - normalize by hand
    # rather than trusting the stored type.
    v = settings.value(key, default)
    if isinstance(v, bool):
        return v
    return str(v).strip().lower() in ("1", "true", "yes")


def replace_all_font_families(data, new_family):
    """Recursively walk a serialized board's JSON (dict/list of dicts -
    see MindMapScene.serialize/BoardCardItem.serialize), overwriting every
    "font_family" value found anywhere (top-level items, their title_font/
    description_font dicts, board-card subitems, table header/data cell
    fonts, arrow labels, ...) with `new_family`, AND rewriting every run
    inside every "*_html" field (text_html, title_html, description_html,
    label_html, ...) to the same family via _force_font_family_in_html.

    Both halves matter: the plain "font_family" keys are only ever read
    back as the *starting* default font when a document is otherwise
    empty, while the actual saved rich text (an item's real, already-
    typed content) carries its own per-run font baked in by Qt's
    toHtml() - swapping just the summary key left every existing note's
    visible font completely unchanged. Deliberately schema-agnostic on
    both counts - every font dict here uses the key "font_family" and
    every rich text field's key ends in "_html", so this one walk covers
    every component type without needing to special-case each one's
    particular field names."""
    if isinstance(data, dict):
        for k, v in data.items():
            if k == "font_family" and isinstance(v, str):
                data[k] = new_family
            elif k.endswith("_html") and isinstance(v, str):
                data[k] = _force_font_family_in_html(v, new_family)
            else:
                replace_all_font_families(v, new_family)
    elif isinstance(data, list):
        for v in data:
            replace_all_font_families(v, new_family)
    return data


class EditableTextItem(QGraphicsTextItem):
    """A QGraphicsTextItem that only grabs mouse input while in edit mode,
    otherwise it lets clicks fall through to its parent component so the
    component can still be selected / dragged / resized normally.

    While *not* in edit mode, a click directly on a checkbox glyph
    (\u2610 / \u2611) at the start of a line toggles it - this is how
    checklist items made via TextNoteItem's context menu get checked off
    without entering text-edit mode."""

    # Set once by MainWindow to the toolbar's font-family combo, so every
    # EditableTextItem (Text Note, plain Text, table cells, arrow labels,
    # media titles/descriptions, ...) can recognize when it's only
    # losing focus *to that combo* (see focusOutEvent below).
    _font_combo = None

    # Set once by MainWindow to a no-arg callable that refreshes the
    # toolbar's Font/B/I/U/Color/Link controls from the live text
    # cursor. The scene's selectionChanged/focusItemChanged signals only
    # fire when which *item* is selected/focused changes, not when the
    # text *cursor*/selection moves within an item that's already being
    # edited - so without this, e.g. dragging to highlight a link inside
    # a note wouldn't light up the Link button the way it should.
    _toolbar_refresh_cb = None

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setFlag(QGraphicsItem.ItemIsFocusable, True)

    def _losing_focus_to_font_combo(self):
        """True while focus is moving to the toolbar's font-family combo
        (its line edit, or its dropdown/completer popup), as opposed to
        moving away to something else entirely (another item, the
        canvas, a different window, ...).

        While the combo's dropdown (or its type-to-search completer's
        popup) is open, Qt reports it via activePopupWidget() regardless
        of which of its internal sub-widgets technically holds focus, so
        that check alone is what actually matters here - enumerating the
        combo's own child widgets by identity is fragile (e.g. the
        popup/container can be set up lazily and not compare equal to
        what's read beforehand)."""
        fc = EditableTextItem._font_combo
        if fc is None:
            return False
        if QApplication.activePopupWidget() is not None:
            return True
        fw = QApplication.focusWidget()
        if fw is None:
            return False
        return fw is fc or fw is fc.lineEdit()

    def focusOutEvent(self, event):
        if self._losing_focus_to_font_combo() or QApplication.activeModalWidget() is not None:
            # Same idea as the font-combo case below: QColorDialog / the
            # Link QInputDialog are modal windows that momentarily steal
            # focus while picking a color or URL for the current
            # selection. Don't drop out of edit mode or clear the
            # selection for that, or by the time the dialog closes and
            # the toolbar action tries to re-read the selection to apply
            # the change, there's nothing left to apply it to.
            # The font-family combo needs real keyboard focus to let the
            # user type/search or use its dropdown list - momentarily
            # taking focus away from whatever text is being edited. Don't
            # actually drop out of edit mode for that: it just makes the
            # cursor/selection blink out and back for no reason. The
            # combo hands focus straight back (see MainWindow's
            # _restore_text_edit_focus / font_combo.hidePopup) once it's
            # done, so editing simply resumes as if nothing happened.
            super().focusOutEvent(event)
            return
        self.setTextInteractionFlags(Qt.NoTextInteraction)
        cursor = self.textCursor()
        cursor.clearSelection()
        self.setTextCursor(cursor)
        super().focusOutEvent(event)

    def mousePressEvent(self, event):
        if self.textInteractionFlags() == Qt.NoTextInteraction:
            if self._toggle_checkbox_at(event.pos()):
                event.accept()
                return
            event.ignore()
            return
        super().mousePressEvent(event)

    def keyPressEvent(self, event):
        if (event.key() == Qt.Key_V and event.modifiers() & Qt.ControlModifier
                and event.modifiers() & Qt.ShiftModifier):
            self._paste_plain_text(event)
            return
        if event.matches(QKeySequence.Paste):
            self._paste_preserving_alignment(event)
            return
        if event.key() in (Qt.Key_Return, Qt.Key_Enter):
            cursor = self.textCursor()
            block_text = cursor.block().text()
            # Which prefix (if any) should continue onto the next line.
            # The current line's own leading glyph is checked *first* -
            # this is what lets Enter correctly continue a bullet/
            # checklist no matter what is hosting this editor (a
            # standalone TextNoteItem, a Board Card's in-place subitem
            # editor via _SubitemTextEdit, ...). Falling back to a
            # "list_mode" flag that only ever lived on TextNoteItem
            # itself meant a checklist Text Note lost auto-continue the
            # moment it was nested inside a Board Card (whose subitem
            # editor has no such flag) - and even after being dragged
            # back out, since subitem_to_component() rebuilds a brand
            # new TextNoteItem whose list_mode always starts back at
            # None regardless of the text's actual checklist content.
            line_prefix = None
            for p in (BULLET_CHAR, CHECK_UNCHECKED, CHECK_CHECKED):
                if block_text.startswith(p + " "):
                    line_prefix = p
                    break
            if line_prefix is None:
                # Nothing typed on this line yet (e.g. right after
                # switching list mode on via the toolbar/context menu on
                # an empty note) - fall back to the owning TextNoteItem's
                # own list_mode for that one case, since there's no
                # glyph yet to read it from.
                parent = self.parentItem()
                mode = getattr(parent, "list_mode", None)
                if mode:
                    line_prefix = BULLET_CHAR if mode == "bullet" else CHECK_UNCHECKED
            if line_prefix:
                prefix = BULLET_CHAR if line_prefix == BULLET_CHAR else CHECK_UNCHECKED
                # Pressing Enter on an already-empty bullet/checklist line
                # exits list mode instead of adding yet another empty one,
                # matching how bullet lists behave in most editors.
                if block_text.strip() in (BULLET_CHAR, CHECK_UNCHECKED, CHECK_CHECKED):
                    cursor.select(QTextCursor.LineUnderCursor)
                    cursor.removeSelectedText()
                    event.accept()
                    return
                cursor.insertText("\n" + prefix + " ")
                self.setTextCursor(cursor)
                event.accept()
                return
        super().keyPressEvent(event)

    def _paste_plain_text(self, event):
        """Ctrl+Shift+V: paste the clipboard's *plain* text only, using
        whatever character formatting is already active at the cursor -
        i.e. exactly as if every character had been typed by hand -
        instead of a normal paste, which carries over the clipboard
        content's own formatting (font, colors, bold/italic runs, links,
        ...) from wherever it was copied from.

        QTextCursor.insertText(str) (with no explicit QTextCharFormat)
        already does this: it stamps the inserted text with the
        cursor's current charFormat and starts a fresh block on each
        "\\n", exactly matching normal keyboard typing - so this is just
        that, fed the clipboard's text instead of a keystroke."""
        text = QApplication.clipboard().text()
        event.accept()
        if not text:
            return
        text = text.replace("\r\n", "\n").replace("\r", "\n")
        cursor = self.textCursor()
        cursor.insertText(text)
        self.setTextCursor(cursor)

    def _paste_preserving_alignment(self, event):
        """Qt's default paste applies whatever paragraph alignment the
        clipboard's rich-text content happens to carry - almost always
        left, since that's what most sources (browsers, other apps)
        default to - silently overwriting whatever alignment the field
        already had, even if it was set to Center/Right beforehand.

        Remember the alignment in force before the paste, let Qt do the
        actual insert as normal, then re-apply that alignment across
        exactly the range that just got pasted in (covering every
        paragraph if the pasted text itself spanned several), so
        pasting never fights the field's existing formatting."""
        cursor = self.textCursor()
        align = cursor.blockFormat().alignment()
        start = min(cursor.position(), cursor.anchor())
        super().keyPressEvent(event)
        end = self.textCursor().position()
        fix_cursor = QTextCursor(self.document())
        fix_cursor.setPosition(start)
        fix_cursor.setPosition(max(start, end), QTextCursor.KeepAnchor)
        block_fmt = fix_cursor.blockFormat()
        block_fmt.setAlignment(align)
        fix_cursor.mergeBlockFormat(block_fmt)
        event.accept()

    def mouseMoveEvent(self, event):
        if self.textInteractionFlags() == Qt.NoTextInteraction:
            event.ignore()
            return
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        super().mouseReleaseEvent(event)
        if self.textInteractionFlags() == Qt.TextEditorInteraction and EditableTextItem._toolbar_refresh_cb:
            EditableTextItem._toolbar_refresh_cb()

    def keyReleaseEvent(self, event):
        super().keyReleaseEvent(event)
        if self.textInteractionFlags() == Qt.TextEditorInteraction and EditableTextItem._toolbar_refresh_cb:
            EditableTextItem._toolbar_refresh_cb()

    def _toggle_checkbox_at(self, pos):
        doc = self.document()
        hit = doc.documentLayout().hitTest(pos, Qt.FuzzyHit)
        if hit < 0:
            return False
        block = doc.findBlock(hit)
        text = block.text()
        if not text[:1] in (CHECK_UNCHECKED, CHECK_CHECKED):
            return False
        # Only react to clicks right on (or just after) the glyph itself,
        # not anywhere else in the line's text.
        if hit - block.position() > 2:
            return False
        new_char = CHECK_CHECKED if text[0] == CHECK_UNCHECKED else CHECK_UNCHECKED
        cur = QTextCursor(block)
        cur.movePosition(QTextCursor.Right, QTextCursor.KeepAnchor, 1)
        cur.insertText(new_char)
        return True


# --------------------------------------------------------------------------
# Base component item: movable / selectable / resizable box
# --------------------------------------------------------------------------

class BaseComponentItem(QGraphicsObject):
    TYPE_NAME = "base"
    DEFAULT_COLOR = None  # subclasses set a sensible default; None = "use built-in look"

    def __init__(self, x=0, y=0, w=200, h=150, item_id=None):
        super().__init__()
        self.id = item_id or new_id()
        self._w = max(1, w)
        self._h = max(1, h)
        self.color = self.DEFAULT_COLOR
        self.setPos(x, y)
        self.setFlags(
            QGraphicsItem.ItemIsMovable
            | QGraphicsItem.ItemIsSelectable
            | QGraphicsItem.ItemSendsGeometryChanges
        )
        self.setAcceptHoverEvents(True)
        self.min_w, self.min_h = 80, 60
        self._resizing = False
        self._resize_start = QPointF()
        self._start_geom = (self._w, self._h)
        # See _raise_to_front_if_needed(): set False at the start of every
        # mousePressEvent, then consumed (set True) the first time this
        # press actually turns into a drag/resize - so a plain click (or
        # double-click, e.g. opening a Board Card) never touches zValue.
        self._raised_this_press = False
        # Board card this item is currently hovering over while being
        # dragged, if any - tracked so we can show/clear the insertion
        # preview line on the target card as the drag moves, instead of
        # only deciding a drop position at release time.
        self._hover_board = None
        # Per-component override of the app-wide Preferences > Default
        # Arrow Snapping Method, set via this item's own context menu
        # (see _add_arrow_snap_menu) - None means "use the app-wide
        # default". Only meaningful for components that can actually be
        # an arrow's anchor target (see ANCHOR_TARGET_TYPES /
        # ArrowItem._effective_snap_method), but harmless to carry on
        # every component type.
        self.arrow_snap_method = None
        self._snap_method_actions = {}

    # -- geometry -----------------------------------------------------
    def boundingRect(self):
        return QRectF(-2, -2, self._w + 4, self._h + 4)

    def rect(self):
        return QRectF(0, 0, self._w, self._h)

    def itemChange(self, change, value):
        if change == QGraphicsItem.ItemPositionHasChanged:
            self._notify_arrows_moved()
        return super().itemChange(change, value)

    def _notify_arrows_moved(self):
        """Tell the scene to re-position any arrow endpoint anchored to
        this item - called whenever this item moves (itemChange above)
        or is resized (set_size below), so an anchored arrow tracks the
        component live instead of only updating on the next drag. Passes
        `self` along as the mover so ArrowItem.refresh_anchors can tell a
        real target component moving (which should re-orbit an anchored
        endpoint to keep facing the arrow's other end) apart from the
        arrow itself moving - which fires this same hook too, since
        ArrowItem is a BaseComponentItem like any other, but must NOT
        re-orbit: see refresh_anchors for why."""
        scene = self.scene()
        if scene is not None and hasattr(scene, "refresh_anchored_arrows"):
            scene.refresh_anchored_arrows(mover=self)

    def set_size(self, w, h):
        self.prepareGeometryChange()
        self._w = max(self.min_w, w)
        self._h = max(self.min_h, h)
        self.on_resized()
        self.update()
        self._notify_arrows_moved()

    def on_resized(self):
        pass

    def set_color(self, color):
        self.color = color.name() if isinstance(color, QColor) else color
        self.update()

    def _frame_pen(self, default="#000000"):
        """Border pen used by image/gif/video items: blue while selected,
        otherwise a fixed thin border - self.color now drives the title/
        description background instead (see
        MediaCardMixin._paint_title_desc_chrome)."""
        if self.isSelected():
            return QPen(QColor("#4c8bf5"), 2)
        return QPen(QColor(default), 1)

    def handle_rect(self):
        return QRectF(self._w - HANDLE_SIZE, self._h - HANDLE_SIZE, HANDLE_SIZE, HANDLE_SIZE)

    def paint_handle(self, painter):
        if self.isSelected():
            painter.setBrush(QColor("#4c8bf5"))
            painter.setPen(QPen(QColor("#ffffff"), 1))
            painter.drawRect(self.handle_rect())

    # -- mouse: resize / drag-drop-onto-board notification ------------
    def _raise_to_front_if_needed(self):
        """Bring this item to front - but only the first time it's
        called for a given mouse press. zValue() is part of serialize()
        (see the "z" field), so unconditionally raising on every
        mousePressEvent - as this used to do - meant a plain click (or
        a double-click to open a Board Card) could change the saved
        JSON snapshot even though nothing the user would call an "edit"
        actually happened, which made the app nag to save changes after
        nothing more than navigating between boards. Now it only fires
        once real dragging/resizing starts (see mouseMoveEvent), and the
        flag is reset back to False at the top of the next
        mousePressEvent."""
        if self._raised_this_press:
            return
        self._raised_this_press = True
        scene = self.scene()
        if scene is not None and hasattr(scene, "bring_to_front"):
            scene.bring_to_front(self)

    def mousePressEvent(self, event):
        self._raised_this_press = False
        if self.isSelected() and self.handle_rect().contains(event.pos()):
            self._resizing = True
            self._resize_start = event.scenePos()
            self._start_geom = (self._w, self._h)
            event.accept()
            return
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if self._resizing:
            self._raise_to_front_if_needed()
            delta = event.scenePos() - self._resize_start
            w0, h0 = self._start_geom
            new_w, new_h = w0 + delta.x(), h0 + delta.y()
            if (event.modifiers() & Qt.ControlModifier) and w0 > 0 and h0 > 0:
                # Constrain to the original width/height ratio, driven by
                # whichever axis the mouse moved further along - the same
                # feel as holding Shift/Ctrl for proportional resize in
                # most design tools.
                aspect = w0 / h0
                if abs(delta.x()) >= abs(delta.y()):
                    new_h = new_w / aspect
                else:
                    new_w = new_h * aspect
            self.set_size(new_w, new_h)
            event.accept()
            return
        self._raise_to_front_if_needed()
        super().mouseMoveEvent(event)
        self._update_board_hover_preview(event.scenePos())

    def _update_board_hover_preview(self, cursor_scene_pos):
        """While this item is being dragged around the canvas (not
        resized), show a live insertion-line preview on whichever board
        card it is currently over, so the user can see exactly where the
        component will land instead of it always jumping to the end of
        the card's contents on drop.

        Uses the actual mouse cursor position rather than this item's
        own geometric center: for a tall/long dragged component, the
        center can sit well outside (below) a board card even while the
        cursor - and the part of the component actually overlapping the
        card - is right at the card's bottom edge, which used to hide
        the insertion line in exactly that case."""
        if isinstance(self, BoardCardItem):
            return
        if isinstance(self, DrawingItem) and not self.allow_board_card:
            # This sketch hasn't opted in (see the "Allow to be Board
            # Card element" toolbar checkbox) - never show the
            # insertion-line preview for it, so it's visually clear
            # while dragging that it simply can't be dropped into a
            # card, matching item_drag_released's own refusal below.
            return
        scene = self.scene()
        if scene is None:
            return
        target = None
        for other in scene.items(cursor_scene_pos):
            if isinstance(other, BoardCardItem) and other is not self:
                target = other
                break
        if target is None:
            # Plain point hit-testing above only ever finds a card
            # whose boundingRect() actually contains the cursor. A card
            # that's been resized down tight enough that its content
            # already reaches its own bottom edge (no free space left
            # under the last subitem) has no point *inside* its bounds
            # that maps to "insert after the last item" - the cursor
            # would have to land on the very last pixel row, which in
            # practice you can't hit. Give every board card's bottom
            # edge a small forgiving strip below it (same width as the
            # card) so hovering just under a tightly-packed card still
            # counts as "insert at the end of that card" instead of the
            # insertion line silently never appearing.
            margin = 24.0
            for other in scene.items():
                if isinstance(other, BoardCardItem) and other is not self:
                    r = other.mapRectToScene(other.rect())
                    band = QRectF(r.left(), r.bottom(), r.width(), margin)
                    if band.contains(cursor_scene_pos):
                        target = other
                        break
        prev = self._hover_board
        if prev is not None and prev is not target:
            prev.clear_insert_preview()
        if target is not None:
            local_y = target.mapFromScene(cursor_scene_pos).y()
            # Clamp into the card's own local range so the fallback in
            # paint() (which draws the line at the bottom of the last
            # subitem's rect once no exact slot is found) is what
            # actually resolves this - a raw local_y from the margin
            # strip above would be > the card's own height.
            local_y = min(local_y, target.rect().height())
            target.show_insert_preview(local_y)
        self._hover_board = target

    def mouseReleaseEvent(self, event):
        was_resizing = self._resizing
        if self._resizing:
            self._resizing = False
            event.accept()
        else:
            super().mouseReleaseEvent(event)
        if was_resizing:
            self._on_resize_interaction_finished()
        hover_board = self._hover_board
        self._hover_board = None
        scene = self.scene()
        if scene is not None and not was_resizing and hasattr(scene, "item_drag_released"):
            scene.item_drag_released(self, hover_board)
        if hover_board is not None:
            hover_board.clear_insert_preview()

    def _on_resize_interaction_finished(self):
        """Hook for subclasses (ImageItem/GifItem) that render at a
        cheaper quality while the resize handle is actively being
        dragged - called once the handle is released, so they can force
        one final high-quality redraw at the now-settled size."""
        pass

    def hoverMoveEvent(self, event):
        if self.isSelected() and self.handle_rect().contains(event.pos()):
            self.setCursor(Qt.SizeFDiagCursor)
        else:
            self.setCursor(Qt.ArrowCursor)
        super().hoverMoveEvent(event)

    # -- context menu (subclasses can extend via the two hooks below) --
    def _build_context_menu(self, menu):
        """Hook for subclasses: add extra QActions to `menu` before the
        standard Duplicate/Delete entries. Store references on self if you
        need to recognize them in _handle_context_action."""
        pass

    def _handle_context_action(self, action):
        """Hook for subclasses: react to an action added in
        _build_context_menu (already-handled Duplicate/Delete/Change Color
        don't reach here)."""
        pass

    def _add_arrow_snap_menu(self, menu):
        """Adds an "Arrow Snapping" submenu with a radio-style choice
        (QActionGroup, mutually exclusive) between the app-wide default
        and each ARROW_SNAP_METHOD_OPTIONS value, for components that can
        be an arrow's anchor target - see ArrowItem._effective_snap_method,
        which consults self.arrow_snap_method (set below) ahead of
        Preferences > Default Arrow Snapping Method."""
        snap_menu = menu.addMenu("Arrow Snapping")
        group = QActionGroup(snap_menu)
        group.setExclusive(True)
        self._snap_method_actions = {}
        current = self.arrow_snap_method
        default_act = snap_menu.addAction("Use Default (Preferences)")
        default_act.setCheckable(True)
        default_act.setChecked(current not in ARROW_SNAP_METHODS)
        group.addAction(default_act)
        self._snap_method_actions[default_act] = None
        for value, label in ARROW_SNAP_METHOD_OPTIONS:
            act = snap_menu.addAction(label)
            act.setCheckable(True)
            act.setChecked(current == value)
            group.addAction(act)
            self._snap_method_actions[act] = value
        menu.addSeparator()

    def contextMenuEvent(self, event):
        menu = QMenu()
        self._build_context_menu(menu)
        if isinstance(self, ANCHOR_TARGET_TYPES):
            self._add_arrow_snap_menu(menu)
        color_action = menu.addAction("Change Color\u2026")
        menu.addSeparator()
        dup_action = menu.addAction("Duplicate")
        del_action = menu.addAction("Delete")
        chosen = menu.exec(event.screenPos())
        if chosen == del_action:
            if self.scene():
                self.scene().removeItem(self)
        elif chosen == dup_action:
            d = self.serialize()
            d["id"] = new_id()
            d["x"] = self.pos().x() + 25
            d["y"] = self.pos().y() + 25
            new_item = deserialize_component(d)
            if new_item and self.scene():
                self.scene().addItem(new_item)
        elif chosen == color_action:
            self._open_color_dialog()
        elif chosen in self._snap_method_actions:
            self.arrow_snap_method = self._snap_method_actions[chosen]
        elif chosen is not None:
            self._handle_context_action(chosen)

    def _open_color_dialog(self):
        """Hook for the context menu's "Change Color..." entry (and mirrored
        by MainWindow.pick_color for the toolbar Color button). Subclasses
        with more than one color - e.g. TableItem - override this to open
        their own settings dialog instead of the plain QColorDialog."""
        start = QColor(self.color) if self.color else QColor("#ffffff")
        color = QColorDialog.getColor(start, None, "Choose component color")
        if color.isValid():
            self.set_color(color)

    # -- serialization --------------------------------------------------
    def serialize(self):
        return {
            "id": self.id,
            "type": self.TYPE_NAME,
            "x": self.pos().x(),
            "y": self.pos().y(),
            "w": self._w,
            "h": self._h,
            "z": self.zValue(),
            "color": self.color,
            "opacity": self.opacity(),
            "arrow_snap_method": self.arrow_snap_method,
        }

    def to_html(self):
        raise NotImplementedError


# --------------------------------------------------------------------------
# Top Strip - an optional colored accent bar along a component's top edge,
# available on Text Note, Image, GIF, Video and Board Card. Implemented as
# a mixin (rather than on BaseComponentItem itself) since it's opt-in per
# type - Drawing/Arrow/Table/PlainText/BoardLink never carry one.
# --------------------------------------------------------------------------

class TopStripMixin:
    """Toggled via the toolbar's "Top Strip" checkbox (shown whenever a
    component of an eligible type is selected) or the context menu entry
    of the same name. While enabled, the component's own Color button/
    "Change Color..." entry opens a two-tab dialog (Background/Top Strip)
    instead of a single plain color picker - see _open_color_dialog below
    and MainWindow.pick_color."""

    TOP_STRIP_H = 5
    DEFAULT_STRIP_COLOR = "#e74c3c"
    # What the two-tab color dialog's first tab should call self.color -
    # "Background" everywhere: a real fill for Text Note/Board Card, and
    # for Image/GIF/Video it's the title/description bar background (see
    # MediaCardMixin._paint_title_desc_chrome). The frame border is a
    # fixed color, independent of self.color (see BaseComponentItem._frame_pen).
    COLOR_TAB_LABEL = "Background"

    def _init_top_strip(self, top_strip_enabled=False, top_strip_color=None):
        self.top_strip_enabled = bool(top_strip_enabled)
        self.top_strip_color = top_strip_color or self.DEFAULT_STRIP_COLOR

    def set_top_strip_color(self, color):
        self.top_strip_color = color.name() if isinstance(color, QColor) else color
        self.update()

    def _toggle_top_strip(self):
        self.top_strip_enabled = not self.top_strip_enabled
        self.update()

    def _paint_top_strip(self, painter, clip_path=None):
        """Call last in paint(), after everything else, so the strip sits
        cleanly on top as a cap across the component's full width. Pass
        the component's own rounded-rect QPainterPath as clip_path (if it
        has one) so the strip's corners follow the component's rounding
        instead of poking square corners out past it."""
        if not getattr(self, "top_strip_enabled", False):
            return
        painter.save()
        if clip_path is not None:
            painter.setClipPath(clip_path)
        painter.setPen(Qt.NoPen)
        painter.setBrush(QColor(self.top_strip_color))
        painter.drawRect(QRectF(0, 0, self._w, self.TOP_STRIP_H))
        painter.restore()

    def _top_strip_serialize(self, d):
        d["top_strip_enabled"] = self.top_strip_enabled
        d["top_strip_color"] = self.top_strip_color
        return d

    def _top_strip_html(self):
        if not getattr(self, "top_strip_enabled", False):
            return ""
        return (f'<div class="top-strip" style="position:absolute;left:0;top:0;right:0;'
                f'height:{self.TOP_STRIP_H}px;background:{self.top_strip_color};"></div>')

    def _build_top_strip_context_menu(self, menu):
        action = menu.addAction("Top Strip")
        action.setCheckable(True)
        action.setChecked(self.top_strip_enabled)
        self._top_strip_menu_action = action

    def _handle_top_strip_context_action(self, action):
        if action is getattr(self, "_top_strip_menu_action", None):
            self._toggle_top_strip()
            return True
        return False

    def _open_color_dialog(self):
        """Overrides BaseComponentItem._open_color_dialog (the context
        menu's "Change Color..." entry point). Always opens the two-tab
        Background/Top Strip dialog, same as MainWindow.pick_color does
        for the toolbar Color button - both color roles are offered
        together regardless of whether the strip is currently switched
        on, so "Change Color..." can set/preview a strip color even
        before the checkbox has ever been ticked."""
        bg, strip = open_bg_strip_color_dialog(
            None,
            QColor(self.color) if getattr(self, "color", None) else QColor(getattr(self, "DEFAULT_COLOR", None) or "#ffffff"),
            QColor(self.top_strip_color),
            bg_label=self.COLOR_TAB_LABEL,
        )
        if bg is not None:
            self.set_color(bg)
            self.set_top_strip_color(strip)


# --------------------------------------------------------------------------
# Text note
# --------------------------------------------------------------------------

class TextNoteItem(TopStripMixin, BaseComponentItem):
    TYPE_NAME = "text"
    DEFAULT_COLOR = "#1e1e1e"
    DEFAULT_TEXT_COLOR = "#e8e8e8"

    TITLE_H = 28

    def __init__(self, x=0, y=0, w=220, h=140, text="New note", color=None, item_id=None,
                 font_family=None, font_size=None, bold=False, italic=False, underline=False,
                 link_url=None, text_color=None, title="Title", show_title=False, title_font=None,
                 text_html=None, title_html=None, top_strip_enabled=False, top_strip_color=None):
        super().__init__(x, y, w, h, item_id)
        self._init_top_strip(top_strip_enabled, top_strip_color)
        self.color = color or self.DEFAULT_COLOR
        # The note's fill/background is self.color (inherited from
        # BaseComponentItem); the text drawn on top of it is a separate
        # color entirely, so the Color picker can target either one
        # depending on whether the whole note or just its text is
        # selected/being edited (see MainWindow.pick_color).
        self.text_color = text_color or self.DEFAULT_TEXT_COLOR
        self.list_mode = None  # None, "bullet" or "checklist" - drives auto-continue on Enter
        # Optional bold header above the body text, off by default -
        # toggled via the "Title" toolbar checkbox / context menu entry.
        self.show_title = bool(show_title)
        # Actual height reserved for the title bar - starts at TITLE_H but
        # grows (see _recalc_title_height) when the title text wraps onto
        # more than one line, so a multi-line title never overlaps the
        # body text below it.
        self._title_h = self.TITLE_H
        self.title_item = EditableTextItem(self)
        self.title_item.setPos(10, 6)
        self.title_item.setTextWidth(max(10, w - 20))
        self.title_item.setDefaultTextColor(QColor(self.text_color))
        self.title_item.setPlainText(title)
        self.title_item.setTextInteractionFlags(Qt.NoTextInteraction)
        self.title_item.setFont(
            _font_from_dict(title_font, base_family="Segoe UI", base_size=12.0, base_bold=True)
            if title_font else QFont("Segoe UI", 12, QFont.Bold)
        )
        self.title_item.setVisible(self.show_title)
        self.title_item.document().contentsChanged.connect(self._on_text_changed)
        self.text_item = EditableTextItem(self)
        self.text_item.setPos(10, self._title_bar_h() + 10)
        self.text_item.setTextWidth(max(10, w - 20))
        self.text_item.setDefaultTextColor(QColor(self.text_color))
        self.text_item.setPlainText(text)
        self.text_item.setTextInteractionFlags(Qt.NoTextInteraction)
        self.text_item.setFont(QFont("Segoe UI", 11))
        self._autosizing = False
        if font_family or font_size or bold or italic or underline:
            _apply_text_font(self, family=font_family, bold=bold, italic=italic,
                              underline=underline, point_size=font_size)
        self.text_item.document().contentsChanged.connect(self._on_text_changed)
        self.link_url = None
        if link_url:
            self.set_link(link_url)
        # Rich per-character formatting (from selection-based toolbar
        # edits) is preserved across save/load as Qt's own document HTML -
        # applied last so it fully overrides the plain-text/whole-font
        # setup above whenever it's present (i.e. loading a board saved
        # by this version of the app).
        if title_html:
            self.title_item.document().setHtml(title_html)
        if text_html:
            self.text_item.document().setHtml(text_html)

    def set_link(self, url):
        """Attach (or, with url=None/empty, remove) a hyperlink to this
        note's text. As with PlainTextItem, this deliberately does not
        touch the text's color - self.text_color (set via
        set_text_color()) remains the single source of truth for what's
        painted and exported, linked or not."""
        self.link_url = normalize_link_url(url) or None

    def set_text_color(self, color):
        self.text_color = color.name() if isinstance(color, QColor) else color
        self.text_item.setDefaultTextColor(QColor(self.text_color))
        self.title_item.setDefaultTextColor(QColor(self.text_color))
        self.update()

    def _title_bar_h(self):
        return self._title_h if self.show_title else 0

    def _recalc_title_height(self):
        """Grow (or shrink back) the title bar to fit however many lines
        the title text currently wraps onto, so a two-or-more-line title
        gets the room it needs instead of being clipped/overlapped by
        the body text underneath it."""
        if not self.show_title:
            self._title_h = self.TITLE_H
            return
        doc_h = self.title_item.document().size().height()
        self._title_h = max(self.TITLE_H, doc_h + 12)

    def _toggle_show_title(self):
        self.show_title = not self.show_title
        self.title_item.setVisible(self.show_title)
        self._on_text_changed()
        self.update()

    def on_resized(self):
        self.title_item.setTextWidth(max(10, self._w - 20))
        self._recalc_title_height()
        self.text_item.setPos(10, self._title_bar_h() + 10)
        self.text_item.setTextWidth(max(10, self._w - 20))

    def _on_text_changed(self):
        # Fit the note's height to its text - grows so typed content
        # never spills outside the visible card, and (unlike before)
        # shrinks back down too, so deleting or shrinking text doesn't
        # leave a big empty note behind. Never shrinks below min_h.
        if self._autosizing:
            return
        self._recalc_title_height()
        doc_h = self.text_item.document().size().height()
        needed_h = doc_h + self._title_bar_h() + 20
        self._autosizing = True
        try:
            self.set_size(self._w, needed_h)
            self.text_item.setPos(10, self._title_bar_h() + 10)
        finally:
            self._autosizing = False

    def paint(self, painter, option, widget=None):
        painter.setRenderHint(QPainter.Antialiasing)
        path = QPainterPath()
        path.addRoundedRect(self.rect(), 8, 8)
        painter.setBrush(QColor(self.color))
        pen = QPen(QColor("#333333") if self.isSelected() else QColor(0, 0, 0, 60),
                   2 if self.isSelected() else 1)
        painter.setPen(pen)
        painter.drawPath(path)
        self._paint_top_strip(painter, clip_path=path)
        self.paint_handle(painter)

    def mouseDoubleClickEvent(self, event):
        if self.show_title and event.pos().y() < self._title_bar_h():
            self.title_item.setTextInteractionFlags(Qt.TextEditorInteraction)
            self.title_item.setFocus()
            cursor = self.title_item.textCursor()
            cursor.select(QTextCursor.Document)
            self.title_item.setTextCursor(cursor)
            event.accept()
            return
        self.text_item.setTextInteractionFlags(Qt.TextEditorInteraction)
        self.text_item.setFocus()
        super().mouseDoubleClickEvent(event)

    def font_targets(self, editing_item=None):
        """What the toolbar's Font/B/I/U/Size controls should restyle:
        just the title while it's the one focused/being edited, otherwise
        the body text - without this, those controls always fall back to
        text_item even while the title is focused (see _apply_text_font's
        default of `[item.text_item]` for items with no font_targets)."""
        if editing_item is self.title_item:
            return [self.title_item]
        return [self.text_item]

    # -- bullet list / checklist formatting -----------------------------
    # Implemented as plain-text line prefixes (rather than Qt's native
    # QTextListFormat) so the formatting survives save/load and HTML
    # export without any extra serialization work - it's just characters
    # in the text.
    def _build_context_menu(self, menu):
        self._title_menu_action = menu.addAction("Title")
        self._title_menu_action.setCheckable(True)
        self._title_menu_action.setChecked(self.show_title)
        self._build_top_strip_context_menu(menu)
        menu.addSeparator()
        self._bullet_menu_action = menu.addAction("Toggle Bullet List")
        self._check_menu_action = menu.addAction("Toggle Checklist")
        menu.addSeparator()

    def _handle_context_action(self, action):
        if action == self._title_menu_action:
            self._toggle_show_title()
        elif self._handle_top_strip_context_action(action):
            pass
        elif action == self._bullet_menu_action:
            self.toggle_bullet_list()
        elif action == self._check_menu_action:
            self.toggle_checklist()

    def toggle_bullet_list(self):
        self._apply_line_prefix(BULLET_CHAR, "bullet")

    def toggle_checklist(self):
        self._apply_line_prefix(CHECK_UNCHECKED, "checklist")

    @staticmethod
    def _line_prefix(line):
        for p in (BULLET_CHAR, CHECK_UNCHECKED, CHECK_CHECKED):
            if line.startswith(p + " "):
                return p
        return None

    def _apply_line_prefix(self, prefix_char, mode_name):
        text = self.text_item.toPlainText()
        lines = text.split("\n")
        non_empty = [ln for ln in lines if ln.strip()]
        # If every non-empty line already has exactly this prefix, treat
        # the click as "turn it off" and strip it back to plain text.
        already = bool(non_empty) and all(self._line_prefix(ln) == prefix_char for ln in non_empty)
        new_lines = []
        for ln in lines:
            existing = self._line_prefix(ln)
            if already:
                new_lines.append(ln[2:] if existing else ln)
            elif existing:
                new_lines.append(prefix_char + " " + ln[2:])
            elif ln.strip():
                new_lines.append(prefix_char + " " + ln)
            else:
                new_lines.append(ln)
        self.text_item.setPlainText("\n".join(new_lines))
        # Turning the list ON arms auto-continue-on-Enter; turning it OFF
        # (already was True before this toggle) disarms it again.
        self.list_mode = None if already else mode_name

    def serialize(self):
        d = super().serialize()
        d["text"] = self.text_item.toPlainText()
        d["title"] = self.title_item.toPlainText()
        d["show_title"] = self.show_title
        d["color"] = self.color
        d["text_color"] = self.text_color
        f = self.text_item.font()
        d["font_family"] = f.family()
        d["font_size"] = f.pointSizeF()
        d["bold"] = f.bold()
        d["italic"] = f.italic()
        d["underline"] = f.underline()
        d["title_font"] = _font_to_dict(self.title_item.font())
        d["link_url"] = self.link_url
        # Full rich-text fidelity (per-character bold/italic/underline/
        # color/font/link runs from selection-based edits) - the plain
        # "text"/"font_family"/... fields above remain as a simple
        # fallback for anything that only reads those.
        d["text_html"] = self.text_item.document().toHtml()
        d["title_html"] = self.title_item.document().toHtml()
        return self._top_strip_serialize(d)

    def to_html(self):
        # Walks the document's actual per-character formatting so the
        # exported HTML mirrors exactly what's shown in the app, run by
        # run - not just one style applied to the whole field.
        f = self.text_item.font()
        text = _qtextdocument_to_web_html(self.text_item.document(),
                                           base_family=f.family(), base_size=f.pointSizeF())
        if not text:
            text = "&nbsp;"
        if self.link_url and not _document_has_anchor(self.text_item.document()):
            # Backward-compat: an older, whole-field-only link (no
            # per-character anchor runs in the document itself).
            safe_url = self.link_url.replace('"', "&quot;")
            text = (f'<a href="{safe_url}" target="_blank" rel="noopener noreferrer" '
                    f'style="color:inherit;text-decoration:underline">{text}</a>')
        bg_css = color_to_css(self.color)
        # self.text_color (set via set_text_color()) is what the app
        # actually paints as this field's default text color - it lives
        # on the QGraphicsTextItem's defaultTextColor(), NOT as a
        # QTextCharFormat.foreground() brush, so _qtextdocument_to_web_html
        # never sees it and emits no color:... for runs the user never
        # explicitly recolored. Without an explicit color here, those
        # runs fell back to the CSS class's own default (#222), which is
        # dark and doesn't match e.g. the app's own light-gray default
        # (#e8e8e8) - explicitly setting it on the wrapper div lets CSS
        # inheritance supply it for every un-colored span underneath.
        text_color_css = color_to_css(self.text_color)
        title_html = ""
        if self.show_title:
            tf = self.title_item.font()
            title_text = _qtextdocument_to_web_html(self.title_item.document(),
                                                      base_family=tf.family(), base_size=tf.pointSizeF())
            title_html = f'<div style="margin-bottom:4px">{title_text}</div>'
        return (
            f'<div class="comp text-note" data-id="{self.id}" style="left:{self.pos().x()}px;top:{self.pos().y()}px;'
            f'width:{self._w}px;height:{self._h}px;background:{bg_css};color:{text_color_css};'
            f'opacity:{self.opacity():.2f}">{self._top_strip_html()}{title_html}{text}</div>'
        )


# --------------------------------------------------------------------------
# Plain text (no frame / no background - just floating text, like a bare
# image with no border)
# --------------------------------------------------------------------------

class PlainTextItem(BaseComponentItem):
    TYPE_NAME = "plaintext"
    DEFAULT_COLOR = "#f2f2f2"  # this is the TEXT color, not a fill

    def __init__(self, x=0, y=0, w=220, h=50, text="Text", color=None, item_id=None,
                 font_family=None, font_size=None, bold=False, italic=False, underline=False,
                 link_url=None, text_html=None):
        super().__init__(x, y, w, h, item_id)
        self.color = color or self.DEFAULT_COLOR
        self.text_item = EditableTextItem(self)
        self.text_item.setPos(4, 4)
        self.text_item.setTextWidth(max(10, w - 8))
        self.text_item.setDefaultTextColor(QColor(self.color))
        self.text_item.setPlainText(text)
        self.text_item.setTextInteractionFlags(Qt.NoTextInteraction)
        self.text_item.setFont(QFont("Segoe UI", 15))
        if font_family or font_size or bold or italic or underline:
            _apply_text_font(self, family=font_family, bold=bold, italic=italic,
                              underline=underline, point_size=font_size)
        self.text_item.document().contentsChanged.connect(self._on_text_changed)
        self._autosizing = False
        self.link_url = None
        if link_url:
            self.set_link(link_url)
        # See TextNoteItem.__init__ - preserves per-character formatting
        # from selection-based toolbar edits across save/load.
        if text_html:
            self.text_item.document().setHtml(text_html)

    def set_link(self, url):
        """Attach (or, with url=None/empty, remove) a hyperlink to this
        note's text. Unlike TextNoteItem, this component's "color" IS its
        text color, so - deliberately - setting a link does NOT force any
        particular color here: whatever self.color already is stays the
        text's color, linked or not, and the Color picker keeps working
        normally on it either way (see set_color). Callers that want the
        classic "new link is blue" affordance apply that themselves right
        when the link is first created (see MainWindow.on_hyperlink_clicked)
        - keeping that one-time default out of this setter means the
        actual displayed/exported color is always exactly self.color, with
        no separate "is it linked" branch to fall out of sync."""
        self.link_url = normalize_link_url(url) or None

    def on_resized(self):
        self.text_item.setTextWidth(max(10, self._w - 8))

    def _on_text_changed(self):
        if self._autosizing:
            return
        doc_h = self.text_item.document().size().height()
        needed_h = doc_h + 8
        if needed_h > self._h:
            self._autosizing = True
            try:
                self.set_size(self._w, needed_h)
            finally:
                self._autosizing = False

    def set_color(self, color):
        # There is no fill on this component - "color" means the text
        # color instead, unlike every other component type. This applies
        # immediately and unconditionally (link or no link) - self.color
        # is the one and only source of truth for what gets painted here
        # AND what to_html() exports, so the two can never disagree.
        self.color = color.name() if isinstance(color, QColor) else color
        self.text_item.setDefaultTextColor(QColor(self.color))
        self.update()

    def paint(self, painter, option, widget=None):
        # Deliberately no background and no border - only a faint dashed
        # outline while selected, purely so the (otherwise invisible) box
        # can still be located, dragged and resized like any component.
        if self.isSelected():
            painter.setRenderHint(QPainter.Antialiasing)
            painter.setPen(QPen(QColor("#4c8bf5"), 1, Qt.DashLine))
            painter.setBrush(Qt.NoBrush)
            painter.drawRect(self.rect())
        self.paint_handle(painter)

    def mouseDoubleClickEvent(self, event):
        self.text_item.setTextInteractionFlags(Qt.TextEditorInteraction)
        self.text_item.setFocus()
        super().mouseDoubleClickEvent(event)

    def serialize(self):
        d = super().serialize()
        d["text"] = self.text_item.toPlainText()
        d["color"] = self.color
        f = self.text_item.font()
        d["font_family"] = f.family()
        d["font_size"] = f.pointSizeF()
        d["bold"] = f.bold()
        d["italic"] = f.italic()
        d["underline"] = f.underline()
        d["link_url"] = self.link_url
        d["text_html"] = self.text_item.document().toHtml()
        return d

    def to_html(self):
        f = self.text_item.font()
        text = _qtextdocument_to_web_html(self.text_item.document(),
                                           base_family=f.family(), base_size=f.pointSizeF())
        if not text:
            text = "&nbsp;"
        if self.link_url and not _document_has_anchor(self.text_item.document()):
            safe_url = self.link_url.replace('"', "&quot;")
            text = (f'<a href="{safe_url}" target="_blank" rel="noopener noreferrer" '
                    f'style="color:inherit;text-decoration:underline">{text}</a>')
        # Same fix as TextNoteItem.to_html above: self.color IS this
        # component's text color (see set_color) but only lives on
        # defaultTextColor(), not in the document's own char formats, so
        # it must be set explicitly here for un-colored runs to inherit
        # it instead of falling back to the browser's default black.
        return (
            f'<div class="comp plain-text-note" data-id="{self.id}" style="left:{self.pos().x()}px;top:{self.pos().y()}px;'
            f'width:{self._w}px;height:{self._h}px;color:{color_to_css(self.color)};'
            f'opacity:{self.opacity():.2f}">{text}</div>'
        )


# --------------------------------------------------------------------------
# Image
# --------------------------------------------------------------------------

class MediaCardMixin:
    """Shared title (top) + description (bottom) chrome for the standalone
    Image/GIF/Video components, so each media component looks like a small
    captioned card - a bold title bar above the media and a plain
    description line below it, both editable in place via double-click,
    the same interaction BoardCardItem already uses for its own title."""

    TITLE_H = 26
    DESC_H = 24
    MIN_MEDIA_H = 40  # smallest room left for the actual media once the
                       # title/description bars have grown to fit their text

    def _init_title_desc(self, title="", description="", show_title=True, show_description=True,
                          title_font=None, desc_font=None, title_color=None, desc_color=None,
                          title_html=None, desc_html=None):
        # Whether the title/description bars are shown at all - toggled
        # via the "Show Title"/"Show Description" context menu entries
        # (see _build_media_context_menu). When both are off, the media
        # itself simply fills the whole component with no chrome.
        self.show_title = True if show_title is None else bool(show_title)
        self.show_description = True if show_description is None else bool(show_description)

        self.title_item = EditableTextItem(self)
        self.title_item.setDefaultTextColor(QColor(title_color) if title_color else QColor("#ffffff"))
        self.title_item.setFont(
            _font_from_dict(title_font, base_family="Segoe UI", base_size=10.0, base_bold=True)
            if title_font else QFont("Segoe UI", 10, QFont.Bold)
        )
        self.title_item.setPlainText(title)
        self.title_item.setTextInteractionFlags(Qt.NoTextInteraction)
        self.title_item.document().setDocumentMargin(4)
        if title_html:
            self.title_item.document().setHtml(title_html)

        self.description_item = EditableTextItem(self)
        self.description_item.setDefaultTextColor(QColor(desc_color) if desc_color else QColor("#aaaaaa"))
        self.description_item.setFont(
            _font_from_dict(desc_font, base_family="Segoe UI", base_size=9.0, base_bold=False)
            if desc_font else QFont("Segoe UI", 9)
        )
        self.description_item.setPlainText(description)
        self.description_item.setTextInteractionFlags(Qt.NoTextInteraction)
        self.description_item.document().setDocumentMargin(4)
        if desc_html:
            self.description_item.document().setHtml(desc_html)

        # Dynamic bar heights - fit the current text/font, growing or
        # shrinking as needed. Recomputed on every text edit
        # (_on_title_desc_text_changed, wired below) and after every
        # toolbar font/size change (see _apply_text_font's hook for
        # _on_title_desc_text_changed).
        self._title_h = self.TITLE_H
        self._desc_h = self.DESC_H
        self._autosizing_td = False
        # Set the text width once up front (needed for an accurate wrapped
        # document height) before measuring, then measure/grow, then lay
        # out again at the now-final bar heights.
        self._layout_title_desc()
        self._recalc_title_desc_heights()
        self._ensure_title_desc_component_height()
        self._layout_title_desc()

        self.title_item.document().contentsChanged.connect(self._on_title_desc_text_changed)
        self.description_item.document().contentsChanged.connect(self._on_title_desc_text_changed)

        self._update_title_desc_visibility()

    def _update_title_desc_visibility(self):
        self.title_item.setVisible(self.show_title)
        self.description_item.setVisible(self.show_description)

    def _title_bar_h(self):
        return self._title_h if self.show_title else 0

    def _desc_bar_h(self):
        return self._desc_h if self.show_description else 0

    def _measure_bar_h(self, item, min_h):
        return max(min_h, item.document().size().height() + 8)

    def _recalc_title_desc_heights(self):
        """Fit the title/description bar heights to their current text
        and font size - grows when there's more content, and (unlike
        TextNoteItem's own height) shrinks back down too, so deleting or
        shrinking text doesn't leave a big empty bar behind."""
        self._title_h = self._measure_bar_h(self.title_item, self.TITLE_H)
        self._desc_h = self._measure_bar_h(self.description_item, self.DESC_H)

    def _ensure_title_desc_component_height(self):
        """Grow the component's overall height if the (possibly now
        taller) title/description bars no longer leave enough room for
        the media itself."""
        needed = self._title_bar_h() + self._desc_bar_h() + self.MIN_MEDIA_H
        if needed > self._h:
            self.prepareGeometryChange()
            self._h = needed

    def _on_title_desc_text_changed(self):
        """Wired to both text items' contentsChanged signal, and also
        called directly as the relayout hook after a toolbar font/size
        change (see _apply_text_font) - either way, the title/description
        frames resize to fit, growing the component if needed."""
        if self._autosizing_td:
            return
        self._autosizing_td = True
        try:
            self._recalc_title_desc_heights()
            self._ensure_title_desc_component_height()
            self._layout_title_desc()
            self.on_resized()
        finally:
            self._autosizing_td = False
        self.update()

    def font_targets(self, editing_item=None):
        """What the toolbar's Font/B/I/U/Size controls should restyle:
        just the title or description currently being edited, if any,
        otherwise both together - the same "whole thing at once"
        behavior Text Note and Table already use."""
        if editing_item is self.title_item or editing_item is self.description_item:
            return [editing_item]
        return [self.title_item, self.description_item]

    def _layout_title_desc(self):
        self.title_item.setPos(4, 0)
        self.title_item.setTextWidth(max(10, self._w - 8))
        self.description_item.setPos(4, self._h - self._desc_bar_h())
        self.description_item.setTextWidth(max(10, self._w - 8))

    def _media_rect(self):
        """The area available for the actual media content, between the
        title bar and the description bar (either or both may be hidden,
        in which case the media simply extends to that edge)."""
        top = self._title_bar_h()
        bottom = self._h - self._desc_bar_h()
        return QRectF(0, top, self._w, max(10, bottom - top))

    def _paint_title_desc_chrome(self, painter):
        painter.setPen(Qt.NoPen)
        painter.setBrush(QColor(self.color) if self.color else QColor("#1e1e1e"))
        if self.show_title:
            painter.drawRect(QRectF(0, 0, self._w, self._title_bar_h()))
        if self.show_description:
            painter.drawRect(QRectF(0, self._h - self._desc_bar_h(), self._w, self._desc_bar_h()))

    def _title_desc_double_click(self, event):
        """Call from the subclass's mouseDoubleClickEvent; returns True if
        the click was on the title/description bar and was handled."""
        y = event.pos().y()
        target = None
        if self.show_title and y < self._title_bar_h():
            target = self.title_item
        elif self.show_description and y > self._h - self._desc_bar_h():
            target = self.description_item
        if target is None:
            return False
        target.setTextInteractionFlags(Qt.TextEditorInteraction)
        target.setFocus()
        cursor = target.textCursor()
        cursor.select(QTextCursor.Document)
        target.setTextCursor(cursor)
        return True

    def _title_desc_serialize(self, d):
        d["title"] = self.title_item.toPlainText()
        d["description"] = self.description_item.toPlainText()
        d["show_title"] = self.show_title
        d["show_description"] = self.show_description
        d["title_font"] = _font_to_dict(self.title_item.font())
        d["description_font"] = _font_to_dict(self.description_item.font())
        d["title_color"] = self.title_item.defaultTextColor().name()
        d["description_color"] = self.description_item.defaultTextColor().name()
        # Full rich-text fidelity (per-character bold/italic/underline/
        # color/highlight runs from selection-based toolbar edits) - see
        # TextNoteItem.serialize for the same pattern. The plain "title"/
        # "description" strings above remain as a simple fallback.
        d["title_html"] = self.title_item.document().toHtml()
        d["description_html"] = self.description_item.document().toHtml()
        return d

    @staticmethod
    def _escape_html(text):
        return (
            (text or "")
            .replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
            .replace("\n", "<br>")
        )

    @staticmethod
    def _font_style_css(font, color):
        # pointSizeF() is a point size, not a pixel size - tagging it "pt"
        # (rather than "px") keeps the exported size in sync with the app,
        # the same fix already applied to the Arrow label's font-size.
        bits = [
            f"font-family:'{font.family()}',sans-serif",
            f"font-size:{font.pointSizeF():.1f}pt",
            f"color:{color}",
        ]
        if font.bold():
            bits.append("font-weight:bold")
        if font.italic():
            bits.append("font-style:italic")
        if font.underline():
            bits.append("text-decoration:underline")
        return ";".join(bits)

    def _title_desc_html(self):
        # Walks each field's actual per-character formatting (same helper
        # TextNoteItem.to_html uses) so highlight/color/bold/italic/
        # underline runs applied via the toolbar survive the HTML export,
        # not just the plain text - the title/description items are live
        # QGraphicsTextItems the whole time, so their document is always
        # up to date here.
        #
        # Both bars also get their own Background fill inlined here (see
        # self.color / set_color, and .media-title/.media-desc's #1e1e1e
        # default in the exported <style> block, which this simply
        # overrides) so a customized background actually shows up in the
        # exported HTML instead of only on the live canvas.
        bg_css = color_to_css(self.color) if self.color else "#1e1e1e"
        title_html = ""
        if self.show_title and self.title_item.toPlainText().strip():
            tf = self.title_item.font()
            title_style = self._font_style_css(tf, self.title_item.defaultTextColor().name()) + f";background:{bg_css}"
            title_text = _qtextdocument_to_web_html(
                self.title_item.document(), base_family=tf.family(), base_size=tf.pointSizeF())
            title_html = f'<div class="media-title" style="{title_style}">{title_text}</div>'
        desc_html = ""
        if self.show_description and self.description_item.toPlainText().strip():
            df = self.description_item.font()
            desc_style = self._font_style_css(df, self.description_item.defaultTextColor().name()) + f";background:{bg_css}"
            desc_text = _qtextdocument_to_web_html(
                self.description_item.document(), base_family=df.family(), base_size=df.pointSizeF())
            desc_html = f'<div class="media-desc" style="{desc_style}">{desc_text}</div>'
        return title_html, desc_html

    # -- toggling title/description on/off, wired up through each media
    # subclass's context menu (see e.g. ImageItem._build_context_menu) --
    def _toggle_show_title(self):
        self.show_title = not self.show_title
        self._update_title_desc_visibility()
        self.on_resized()
        self.update()

    def _toggle_show_description(self):
        self.show_description = not self.show_description
        self._update_title_desc_visibility()
        self.on_resized()
        self.update()

    def _build_media_context_menu(self, menu):
        """Call from the subclass's _build_context_menu override to add
        the "Show Title"/"Show Description" checkable entries."""
        title_action = menu.addAction("Show Title")
        title_action.setCheckable(True)
        title_action.setChecked(self.show_title)
        desc_action = menu.addAction("Show Description")
        desc_action.setCheckable(True)
        desc_action.setChecked(self.show_description)
        self._build_top_strip_context_menu(menu)
        menu.addSeparator()
        self._media_title_action = title_action
        self._media_desc_action = desc_action

    def _handle_media_context_action(self, action):
        """Call from the subclass's _handle_context_action override;
        returns True if the action was one of ours and was handled."""
        if action is getattr(self, "_media_title_action", None):
            self._toggle_show_title()
            return True
        if action is getattr(self, "_media_desc_action", None):
            self._toggle_show_description()
            return True
        if self._handle_top_strip_context_action(action):
            return True
        return False


class ImageItem(TopStripMixin, MediaCardMixin, BaseComponentItem):
    TYPE_NAME = "image"
    DEFAULT_COLOR = "#1e1e1e"  # title/description bar background fill (see
                                # MediaCardMixin._paint_title_desc_chrome) -
                                # matches TextNoteItem's default.
    COLOR_TAB_LABEL = "Background"

    def __init__(self, x=0, y=0, w=240, h=180, pixmap=None, b64=None, item_id=None,
                 title="", description="", show_title=True, show_description=True,
                 title_font=None, desc_font=None, title_color=None, desc_color=None,
                 title_html=None, desc_html=None,
                 top_strip_enabled=False, top_strip_color=None):
        super().__init__(x, y, w, h, item_id)
        # Media cards tend to be large on screen, so during panning they
        # fall inside the newly-exposed strip on almost every mouse-move
        # step, re-running the whole paint() (background rect, image draw,
        # title/description child items, border, handle) dozens of times
        # a second even though none of that content actually changed -
        # only the item's screen position did. DeviceCoordinateCache
        # renders once and reuses that cached pixmap for pure translation/
        # scroll, which is what was making panning stutter specifically on
        # canvases with image/gif/video cards. update() (called whenever
        # the pixmap, text, or size genuinely changes) still invalidates
        # and re-renders the cache as normal.
        self.setCacheMode(QGraphicsItem.DeviceCoordinateCache)
        self._init_top_strip(top_strip_enabled, top_strip_color)
        self.pixmap_orig = pixmap if pixmap is not None else base64_to_pixmap(b64)
        # Cache of the last smooth-scaled pixmap, keyed by target size -
        # scaling a full-resolution photo is expensive, and paint() can be
        # called on every scene repaint (cursor blink elsewhere, another
        # item animating, mouse move, ...), not just when this image
        # actually changes. Without caching, a single large imported photo
        # re-does that expensive scale dozens of times a second and stalls
        # the whole app, not just this item.
        self._scaled_cache_pixmap = None
        self._scaled_cache_size = None
        self._scaled_cache_mode = None
        # Cache of the PNG/base64 encoding of pixmap_orig - encoding a
        # full-resolution photo to PNG is real CPU work, and serialize()
        # runs far more often than the pixmap itself actually changes:
        # every debounced undo checkpoint (scene.changed, ~every settled
        # drag/edit) and every unsaved-changes check re-serializes the
        # whole board. Clicking to pick the item up for a drag flushes
        # any pending checkpoint immediately (see MainWindow's
        # _flush_pending_undo_checkpoint), so without this cache that
        # PNG re-encode was happening synchronously right as a drag
        # begins - the actual source of "dragging feels expensive".
        # When loading from a saved board file, `b64` IS already the
        # exact PNG bytes we want serialize() to hand back - seed the
        # cache with it directly instead of throwing it away and making
        # the very next serialize()/undo-snapshot decode-then-re-encode
        # every single image on the board from scratch (this was the
        # main reason opening a board with photos took so long).
        self._b64_cache = b64 if pixmap is None else None
        self.min_w, self.min_h = 120, 140
        self.setAcceptDrops(True)
        self._init_title_desc(title, description, show_title, show_description,
                               title_font=title_font, desc_font=desc_font,
                               title_color=title_color, desc_color=desc_color,
                               title_html=title_html, desc_html=desc_html)

    def set_pixmap(self, pixmap):
        self.pixmap_orig = pixmap
        self._scaled_cache_pixmap = None
        self._scaled_cache_size = None
        self._scaled_cache_mode = None
        self._b64_cache = None
        self.update()

    def _get_b64(self):
        if self._b64_cache is None:
            self._b64_cache = pixmap_to_base64(self.pixmap_orig)
        return self._b64_cache

    def _on_resize_interaction_finished(self):
        # The handle was just released after possibly several frames of
        # cheap Qt.FastTransformation scaling (see paint()) - drop the
        # cache so the very next paint redoes one final, high-quality
        # smooth scale at the settled size instead of leaving the
        # blocky/aliased fast-mode result on screen at rest.
        self._scaled_cache_pixmap = None
        self._scaled_cache_size = None
        self._scaled_cache_mode = None
        self.update()

    def on_resized(self):
        self._layout_title_desc()

    def mouseDoubleClickEvent(self, event):
        if self._title_desc_double_click(event):
            event.accept()
            return
        super().mouseDoubleClickEvent(event)

    def _build_context_menu(self, menu):
        save_action = menu.addAction("Save Image\u2026")
        menu.addSeparator()
        self._save_media_action = save_action
        self._build_media_context_menu(menu)

    def _handle_context_action(self, action):
        if action is getattr(self, "_save_media_action", None):
            self._save_image_to_disk()
            return
        self._handle_media_context_action(action)

    def _save_image_to_disk(self):
        """Context-menu handler: write the full-resolution pixmap to a
        file the user picks on disk."""
        if self.pixmap_orig.isNull():
            QMessageBox.information(None, "Save Image", "There is no image to save.")
            return
        path, _ = QFileDialog.getSaveFileName(
            None, "Save Image", "image.png",
            "PNG (*.png);;JPEG (*.jpg *.jpeg);;BMP (*.bmp);;WEBP (*.webp)",
        )
        if not path:
            return
        if not os.path.splitext(path)[1]:
            path += ".png"
        if not self.pixmap_orig.save(path):
            QMessageBox.warning(None, "Save Image", f"Failed to save image to:\n{path}")

    def paint(self, painter, option, widget=None):
        painter.setRenderHint(QPainter.SmoothPixmapTransform)
        rect = self._media_rect()
        painter.setBrush(QColor("#111111"))
        painter.setPen(Qt.NoPen)
        painter.drawRect(rect)
        if not self.pixmap_orig.isNull():
            target_size = rect.size().toSize()
            # Nearest-neighbor while the resize handle is actively being
            # dragged (set_size()/on_resized() fire on every mouse-move,
            # so the target size - and thus the cache - genuinely changes
            # every frame here; a full bilinear smooth scale of a large
            # photo on every one of those frames is what made resizing
            # feel heavy). One high-quality smooth pass happens via
            # _on_resize_interaction_finished() once the handle is let go.
            mode = Qt.FastTransformation if self._resizing else Qt.SmoothTransformation
            if (self._scaled_cache_pixmap is None or self._scaled_cache_size != target_size
                    or self._scaled_cache_mode != mode):
                self._scaled_cache_pixmap = self.pixmap_orig.scaled(
                    target_size, Qt.KeepAspectRatio, mode
                )
                self._scaled_cache_size = target_size
                self._scaled_cache_mode = mode
            scaled = self._scaled_cache_pixmap
            px = rect.x() + (rect.width() - scaled.width()) / 2
            py = rect.y() + (rect.height() - scaled.height()) / 2
            painter.drawPixmap(int(px), int(py), scaled)
        else:
            painter.setPen(QColor("#888888"))
            painter.drawText(rect, Qt.AlignCenter, "Image")
        self._paint_title_desc_chrome(painter)
        painter.setPen(self._frame_pen("#000000"))
        painter.setBrush(Qt.NoBrush)
        painter.drawRect(self.rect())
        self._paint_top_strip(painter)
        self.paint_handle(painter)

    def dragEnterEvent(self, event):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()

    def dragMoveEvent(self, event):
        event.acceptProposedAction()

    def dropEvent(self, event):
        urls = event.mimeData().urls()
        if urls:
            path = urls[0].toLocalFile()
            pm = QPixmap(path)
            if not pm.isNull():
                self.set_pixmap(pm)
        event.acceptProposedAction()

    def serialize(self):
        d = super().serialize()
        d["data"] = self._get_b64()
        return self._top_strip_serialize(self._title_desc_serialize(d))

    def to_html(self):
        b64 = self._get_b64()
        title_html, desc_html = self._title_desc_html()
        return (
            f'<div class="comp image-note" data-id="{self.id}" style="left:{self.pos().x()}px;top:{self.pos().y()}px;'
            f'width:{self._w}px;height:{self._h}px;">{self._top_strip_html()}{title_html}'
            f'<img src="data:image/png;base64,{b64}" />{desc_html}</div>'
        )


# --------------------------------------------------------------------------
# GIF (animated)
# --------------------------------------------------------------------------

class GifItem(TopStripMixin, MediaCardMixin, BaseComponentItem):
    TYPE_NAME = "gif"
    DEFAULT_COLOR = "#1e1e1e"
    COLOR_TAB_LABEL = "Background"

    def __init__(self, x=0, y=0, w=240, h=180, gif_bytes=None, b64=None, item_id=None,
                 title="", description="", show_title=True, show_description=True,
                 title_font=None, desc_font=None, title_color=None, desc_color=None,
                 title_html=None, desc_html=None,
                 top_strip_enabled=False, top_strip_color=None):
        super().__init__(x, y, w, h, item_id)
        # See ImageItem.__init__ for why this cache mode matters for
        # panning smoothness - same reasoning applies here, and the GIF's
        # own animation update() calls still invalidate/refresh the cache
        # normally, so the animation keeps playing correctly.
        self.setCacheMode(QGraphicsItem.DeviceCoordinateCache)
        self._init_top_strip(top_strip_enabled, top_strip_color)
        if gif_bytes is not None:
            self.gif_bytes = gif_bytes
        elif b64:
            self.gif_bytes = base64.b64decode(b64)
        else:
            self.gif_bytes = b""
        self.buffer = None
        self.movie = None
        self._current_pixmap = QPixmap()
        self._scaled_cache_pixmap = None
        self._scaled_cache_size = None
        self._scaled_cache_mode = None
        self.min_w, self.min_h = 120, 140
        self.setAcceptDrops(True)
        self._init_title_desc(title, description, show_title, show_description,
                               title_font=title_font, desc_font=desc_font,
                               title_color=title_color, desc_color=desc_color,
                               title_html=title_html, desc_html=desc_html)
        self._setup_movie()

    def _setup_movie(self):
        if not self.gif_bytes:
            return
        self.buffer = QBuffer(self)
        self.buffer.setData(self.gif_bytes)
        self.buffer.open(QIODevice.ReadOnly)
        self.movie = QMovie(self)
        self.movie.setDevice(self.buffer)
        self.movie.frameChanged.connect(self._on_frame)
        self.movie.start()

    def _on_frame(self, _frame_no):
        if self.movie:
            self._current_pixmap = self.movie.currentPixmap()
            self._scaled_cache_pixmap = None
            self._scaled_cache_size = None
            self._scaled_cache_mode = None
            self.update()

    def _on_resize_interaction_finished(self):
        self._scaled_cache_pixmap = None
        self._scaled_cache_size = None
        self._scaled_cache_mode = None
        self.update()

    def set_gif_bytes(self, data):
        if self.movie:
            self.movie.stop()
        self.gif_bytes = data
        self._setup_movie()

    def itemChange(self, change, value):
        if change == QGraphicsItem.ItemSceneHasChanged and value is None:
            # This item just left the scene (a component deleted, or a
            # whole board torn down by MindMapScene.clear_board() - e.g.
            # navigating to another board and back). Same reasoning as
            # VideoItem.itemChange: self.movie is a QMovie whose
            # frameChanged is connected to self._on_frame, and that
            # connection keeps this GifItem's Python wrapper (and thus
            # its underlying C++ object) alive for as long as the movie
            # keeps running - nothing here stopped it on scene removal.
            # A frame delivered after removal still just no-ops safely
            # against a scene-less item, but if it lands squarely in the
            # middle of the scene's own C++ teardown it can hit a
            # partially-destroyed item instead, which is undefined
            # behavior - a native crash with no Python traceback, not a
            # catchable exception. Stopping the movie here, synchronously
            # and immediately, closes that window. Safe to call even if
            # the movie was never started, and safe to call again later.
            if self.movie is not None:
                self.movie.stop()
        return super().itemChange(change, value)

    def on_resized(self):
        self._layout_title_desc()

    def mouseDoubleClickEvent(self, event):
        if self._title_desc_double_click(event):
            event.accept()
            return
        super().mouseDoubleClickEvent(event)

    def _build_context_menu(self, menu):
        save_action = menu.addAction("Save GIF\u2026")
        menu.addSeparator()
        self._save_media_action = save_action
        self._build_media_context_menu(menu)

    def _handle_context_action(self, action):
        if action is getattr(self, "_save_media_action", None):
            self._save_gif_to_disk()
            return
        self._handle_media_context_action(action)

    def _save_gif_to_disk(self):
        """Context-menu handler: write the raw GIF bytes to a file the
        user picks on disk."""
        if not self.gif_bytes:
            QMessageBox.information(None, "Save GIF", "There is no GIF to save.")
            return
        path, _ = QFileDialog.getSaveFileName(None, "Save GIF", "image.gif", "GIF (*.gif)")
        if not path:
            return
        if not path.lower().endswith(".gif"):
            path += ".gif"
        try:
            with open(path, "wb") as f:
                f.write(self.gif_bytes)
        except OSError as e:
            QMessageBox.warning(None, "Save GIF", f"Failed to save GIF to:\n{path}\n\n{e}")

    def paint(self, painter, option, widget=None):
        rect = self._media_rect()
        painter.setBrush(QColor("#111111"))
        painter.setPen(Qt.NoPen)
        painter.drawRect(rect)
        if not self._current_pixmap.isNull():
            target_size = rect.size().toSize()
            mode = Qt.FastTransformation if self._resizing else Qt.SmoothTransformation
            if (self._scaled_cache_pixmap is None or self._scaled_cache_size != target_size
                    or self._scaled_cache_mode != mode):
                self._scaled_cache_pixmap = self._current_pixmap.scaled(
                    target_size, Qt.KeepAspectRatio, mode
                )
                self._scaled_cache_size = target_size
                self._scaled_cache_mode = mode
            scaled = self._scaled_cache_pixmap
            px = rect.x() + (rect.width() - scaled.width()) / 2
            py = rect.y() + (rect.height() - scaled.height()) / 2
            painter.drawPixmap(int(px), int(py), scaled)
        else:
            painter.setPen(QColor("#888888"))
            painter.drawText(rect, Qt.AlignCenter, "GIF")
        self._paint_title_desc_chrome(painter)
        painter.setPen(self._frame_pen("#000000"))
        painter.setBrush(Qt.NoBrush)
        painter.drawRect(self.rect())
        self._paint_top_strip(painter)
        self.paint_handle(painter)

    def dragEnterEvent(self, event):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()

    def dragMoveEvent(self, event):
        event.acceptProposedAction()

    def dropEvent(self, event):
        urls = event.mimeData().urls()
        if urls:
            path = urls[0].toLocalFile()
            try:
                with open(path, "rb") as f:
                    data = f.read()
                self.set_gif_bytes(data)
            except Exception:
                pass
        event.acceptProposedAction()

    def serialize(self):
        d = super().serialize()
        d["data"] = base64.b64encode(self.gif_bytes).decode("ascii") if self.gif_bytes else ""
        return self._top_strip_serialize(self._title_desc_serialize(d))

    def to_html(self):
        b64 = base64.b64encode(self.gif_bytes).decode("ascii") if self.gif_bytes else ""
        title_html, desc_html = self._title_desc_html()
        return (
            f'<div class="comp gif-note" data-id="{self.id}" style="left:{self.pos().x()}px;top:{self.pos().y()}px;'
            f'width:{self._w}px;height:{self._h}px;">{self._top_strip_html()}{title_html}'
            f'<img src="data:image/gif;base64,{b64}" />{desc_html}</div>'
        )


# --------------------------------------------------------------------------
# Video
# --------------------------------------------------------------------------

class VideoPlayerNode(QGraphicsObject):
    """The actual video render surface + play/pause/seek/time/mute
    controls, shared by both the standalone VideoItem and every "video"
    subitem embedded in a BoardCardItem (see
    BoardCardItem._get_or_create_video_proxy) - so the same real
    controls, and the same actually-visible video frames, show up in
    both places instead of only on the standalone component.

    This is a plain QGraphicsItem (not a QWidget), because the frames
    themselves are drawn with QGraphicsVideoItem, a genuine QGraphicsItem
    the scene paints directly - a QVideoWidget embedded through a
    QGraphicsProxyWidget reliably rendered as solid black here (audio,
    the seek bar, and the time counter all worked fine - only the frames
    never appeared), because QVideoWidget owns its own native/GPU
    surface that a proxy widget's paint()-based compositing can't
    correctly capture. Only the small control bar (buttons + slider)
    still needs an embedded QWidget, via its own small proxy."""

    CONTROLS_H = 26

    def __init__(self, video_bytes=None, parent=None):
        super().__init__(parent)
        self._w = 160
        self._h = 120
        self._tmp_file = None
        self.player = None
        self.audio = None
        self.video_item = None
        self._no_media_label = None
        self._seeking = False  # true while the user is dragging the seek
                                # slider, so incoming positionChanged
                                # updates don't fight the drag

        if HAS_MULTIMEDIA:
            self.video_item = QGraphicsVideoItem(self)
            self.video_item.setAspectRatioMode(Qt.KeepAspectRatio)
            # Parented to self (a QObject, via QGraphicsObject) mainly
            # as a second line of defense: the itemChange() override
            # above is what actually stops playback and detaches the
            # video output the instant this node leaves a scene, but
            # giving these an explicit Qt parent also means a normal
            # Qt-side deleteLater()/destructor cascade cleans them up
            # correctly even in some other, unforeseen teardown path
            # that doesn't go through removeItem().
            self.player = QMediaPlayer(self)
            self.audio = QAudioOutput(self)
            self.player.setAudioOutput(self.audio)
            self.player.setVideoOutput(self.video_item)
            self.player.playbackStateChanged.connect(self._on_playback_state_changed)
            self.player.positionChanged.connect(self._on_position_changed)
            self.player.durationChanged.connect(self._on_duration_changed)
        else:
            self._no_media_label = QGraphicsTextItem(
                "Video preview unavailable\n(QtMultimedia not installed)", self)
            self._no_media_label.setDefaultTextColor(QColor("#888888"))

        controls = QWidget()
        c_layout = QHBoxLayout(controls)
        c_layout.setContentsMargins(4, 0, 4, 0)
        c_layout.setSpacing(4)

        self.play_btn = QPushButton("\u25B6")
        self.play_btn.setFixedWidth(26)
        self.play_btn.clicked.connect(self.toggle_play)
        c_layout.addWidget(self.play_btn)

        self.position_slider = QSlider(Qt.Horizontal)
        self.position_slider.setRange(0, 0)
        self.position_slider.sliderPressed.connect(self._on_seek_start)
        self.position_slider.sliderMoved.connect(self._on_seek_move)
        self.position_slider.sliderReleased.connect(self._on_seek_end)
        c_layout.addWidget(self.position_slider, 1)

        self.time_label = QLabel("0:00 / 0:00")
        self.time_label.setStyleSheet("color:#bbb; font-size:11px;")
        self.time_label.setFixedWidth(80)
        c_layout.addWidget(self.time_label)

        self.mute_btn = QPushButton("\U0001F50A")
        self.mute_btn.setFixedWidth(26)
        self.mute_btn.clicked.connect(self.toggle_mute)
        c_layout.addWidget(self.mute_btn)

        controls.setStyleSheet(
            "QSlider::groove:horizontal { height:4px; background:#444; border-radius:2px; }"
            "QSlider::handle:horizontal { width:10px; margin:-4px 0; background:#4c8bf5; border-radius:5px; }"
            "QPushButton { background:#333; color:#eee; border:none; border-radius:3px; }"
            "QPushButton:hover { background:#454545; }"
        )
        if not HAS_MULTIMEDIA:
            self.play_btn.setEnabled(False)
            self.position_slider.setEnabled(False)
            self.mute_btn.setEnabled(False)

        self.controls_proxy = QGraphicsProxyWidget(self)
        self.controls_proxy.setWidget(controls)
        # The controls are a real styled QWidget (QSS-rendered buttons and
        # slider) re-rasterized via the style engine on every repaint. That
        # cost is fine for a single static paint, but during panning the
        # view repaints continuously while the widget's actual content
        # never changes - only its screen position does. Caching the
        # rendered pixmap here means panning just blits it instead of
        # re-running the whole widget/style paint pipeline every frame,
        # which is what caused the stutter on canvases with video/media
        # cards (this cache is still invalidated automatically whenever the
        # widget's content genuinely changes, e.g. play/pause icon, slider
        # position, or time label text).
        self.controls_proxy.setCacheMode(QGraphicsItem.DeviceCoordinateCache)

        self.resize(self._w, self._h)
        if video_bytes:
            self.set_video_bytes(video_bytes)

    def boundingRect(self):
        return QRectF(0, 0, self._w, self._h)

    def itemChange(self, change, value):
        if change == QGraphicsItem.ItemSceneHasChanged and value is None:
            # This item (or an ancestor - e.g. the whole VideoItem, or
            # the BoardCardItem a "video" subitem's node is parented
            # to) just left the scene: a component deleted, or an
            # entire board torn down (MindMapScene.clear_board(), e.g.
            # navigating to another board and back). self.video_item is
            # a genuine QGraphicsItem *child* of this node, so Qt's own
            # C++ item-tree teardown destroys it automatically and in
            # sync with this node. self.player/self.audio are not -
            # QMediaPlayer()/QAudioOutput() above were created with no
            # Qt parent at all, so nothing otherwise stops them from
            # outliving self.video_item by even a fraction of a second.
            # A still-playing player's decode/render backend runs on
            # its own thread and can be mid-delivery of the *next*
            # frame to that already-destroyed video sink the moment
            # this fires - a native crash with no Python traceback,
            # since it happens entirely on that backend thread rather
            # than through any Python call Claude/CPython could catch.
            # Stopping and detaching the output here, synchronously and
            # immediately on scene removal, closes that window. Safe to
            # call even when playback was already stopped, and safe to
            # call again afterwards (e.g. BoardCardItem._prune_video_
            # proxies also calls player.stop() directly for its own,
            # narrower "dragged this subitem out" case).
            if self.player is not None:
                self.player.stop()
                self.player.setVideoOutput(None)
        return super().itemChange(change, value)

    def paint(self, painter, option, widget=None):
        painter.setPen(Qt.NoPen)
        painter.setBrush(QColor("#000000"))
        painter.drawRect(self.boundingRect())

    def resize(self, w, h):
        self.prepareGeometryChange()
        self._w = max(10, w)
        self._h = max(10, h)
        video_h = max(10, self._h - self.CONTROLS_H)
        if self.video_item is not None:
            self.video_item.setPos(0, 0)
            self.video_item.setSize(QSizeF(self._w, video_h))
        if self._no_media_label is not None:
            self._no_media_label.setTextWidth(self._w - 12)
            self._no_media_label.setPos(6, max(0, video_h / 2 - 20))
        self.controls_proxy.setPos(0, video_h)
        self.controls_proxy.resize(self._w, self.CONTROLS_H)
        self.update()

    def set_video_bytes(self, data):
        if not HAS_MULTIMEDIA or not data or self.player is None:
            return
        fd, path = tempfile.mkstemp(suffix=".mp4")
        with os.fdopen(fd, "wb") as f:
            f.write(data)
        self._tmp_file = path
        _TEMP_VIDEO_FILES.append(path)
        self.player.setSource(QUrl.fromLocalFile(path))

    def toggle_play(self):
        if not self.player:
            return
        if self.player.playbackState() == QMediaPlayer.PlayingState:
            self.player.pause()
        else:
            self.player.play()

    def toggle_mute(self):
        if not self.audio:
            return
        muted = not self.audio.isMuted()
        self.audio.setMuted(muted)
        self.mute_btn.setText("\U0001F507" if muted else "\U0001F50A")

    def _on_playback_state_changed(self, state):
        self.play_btn.setText("\u23F8" if state == QMediaPlayer.PlayingState else "\u25B6")

    @staticmethod
    def _fmt_ms(ms):
        secs = max(0, int(ms / 1000))
        m, s = divmod(secs, 60)
        return f"{m}:{s:02d}"

    def _on_position_changed(self, pos):
        if not self._seeking:
            self.position_slider.blockSignals(True)
            self.position_slider.setValue(pos)
            self.position_slider.blockSignals(False)
            self.time_label.setText(f"{self._fmt_ms(pos)} / {self._fmt_ms(self.player.duration())}")

    def _on_duration_changed(self, dur):
        self.position_slider.setRange(0, dur)
        self.time_label.setText(f"{self._fmt_ms(self.player.position())} / {self._fmt_ms(dur)}")

    def _on_seek_start(self):
        self._seeking = True

    def _on_seek_move(self, value):
        self.time_label.setText(f"{self._fmt_ms(value)} / {self._fmt_ms(self.player.duration())}")

    def _on_seek_end(self):
        if self.player:
            self.player.setPosition(self.position_slider.value())
        self._seeking = False


class VideoItem(TopStripMixin, MediaCardMixin, BaseComponentItem):
    TYPE_NAME = "video"
    DEFAULT_COLOR = "#1e1e1e"
    COLOR_TAB_LABEL = "Background"
    DRAG_STRIP_H = 16

    def __init__(self, x=0, y=0, w=320, h=220, video_bytes=None, b64=None, item_id=None,
                 title="", description="", show_title=True, show_description=True,
                 title_font=None, desc_font=None, title_color=None, desc_color=None,
                 title_html=None, desc_html=None,
                 top_strip_enabled=False, top_strip_color=None):
        super().__init__(x, y, w, h, item_id)
        # See ImageItem.__init__ for why this cache mode matters for
        # panning smoothness. This only caches the card's own chrome
        # (background, drag strip, border, title/description); the actual
        # video frames are painted by self.player_node, a separate child
        # item with its own independent cache mode, so playback still
        # updates every frame as normal.
        self.setCacheMode(QGraphicsItem.DeviceCoordinateCache)
        self._init_top_strip(top_strip_enabled, top_strip_color)
        if video_bytes is not None:
            self.video_bytes = video_bytes
        elif b64:
            self.video_bytes = base64.b64decode(b64)
        else:
            self.video_bytes = b""
        self.min_w, self.min_h = 200, 220
        self.player_node = VideoPlayerNode(self.video_bytes, parent=self)
        self.setAcceptDrops(True)
        self._init_title_desc(title, description, show_title, show_description,
                               title_font=title_font, desc_font=desc_font,
                               title_color=title_color, desc_color=desc_color,
                               title_html=title_html, desc_html=desc_html)
        self._resize_player()

    def _resize_player(self):
        inset = 4
        media = self._media_rect()
        self.player_node.setPos(media.x() + inset, media.y() + self.DRAG_STRIP_H)
        w = max(10, media.width() - inset * 2)
        h = max(10, media.height() - self.DRAG_STRIP_H - inset)
        self.player_node.resize(w, h)

    def on_resized(self):
        self._layout_title_desc()
        self._resize_player()

    def mouseDoubleClickEvent(self, event):
        if self._title_desc_double_click(event):
            event.accept()
            return
        super().mouseDoubleClickEvent(event)

    def set_video_bytes(self, data):
        self.video_bytes = data
        self.player_node.set_video_bytes(data)

    def _build_context_menu(self, menu):
        save_action = menu.addAction("Save Video\u2026")
        menu.addSeparator()
        self._save_media_action = save_action
        self._build_media_context_menu(menu)

    def _handle_context_action(self, action):
        if action is getattr(self, "_save_media_action", None):
            self._save_video_to_disk()
            return
        self._handle_media_context_action(action)

    def _save_video_to_disk(self):
        """Context-menu handler: write the raw video bytes to a file the
        user picks on disk."""
        if not self.video_bytes:
            QMessageBox.information(None, "Save Video", "There is no video to save.")
            return
        path, _ = QFileDialog.getSaveFileName(
            None, "Save Video", "video.mp4",
            "Video (*.mp4 *.mov *.avi *.webm *.mkv)",
        )
        if not path:
            return
        if not os.path.splitext(path)[1]:
            path += ".mp4"
        try:
            with open(path, "wb") as f:
                f.write(self.video_bytes)
        except OSError as e:
            QMessageBox.warning(None, "Save Video", f"Failed to save video to:\n{path}\n\n{e}")

    def paint(self, painter, option, widget=None):
        media = self._media_rect()
        painter.setBrush(QColor("#000000"))
        painter.setPen(Qt.NoPen)
        painter.drawRect(media)
        # drag strip, inside the media area, above the player - grabbing
        # this (instead of the player widget) lets the whole component
        # still be moved/reordered/dragged out without fighting the
        # player's own play/seek/mute controls for clicks
        strip = QRectF(media.x(), media.y(), media.width(), self.DRAG_STRIP_H)
        painter.setBrush(QColor("#1e1e1e"))
        painter.drawRect(strip)
        painter.setBrush(QColor("#666666"))
        cx = strip.center().x()
        cy = strip.center().y()
        for i in (-10, 0, 10):
            painter.drawEllipse(QPointF(cx + i, cy), 1.5, 1.5)
        self._paint_title_desc_chrome(painter)
        painter.setPen(self._frame_pen("#000000"))
        painter.setBrush(Qt.NoBrush)
        painter.drawRect(self.rect())
        self._paint_top_strip(painter)
        self.paint_handle(painter)

    def dragEnterEvent(self, event):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()

    def dragMoveEvent(self, event):
        event.acceptProposedAction()

    def dropEvent(self, event):
        urls = event.mimeData().urls()
        if urls:
            path = urls[0].toLocalFile()
            try:
                with open(path, "rb") as f:
                    data = f.read()
                self.set_video_bytes(data)
            except Exception:
                pass
        event.acceptProposedAction()

    def serialize(self):
        d = super().serialize()
        d["data"] = base64.b64encode(self.video_bytes).decode("ascii") if self.video_bytes else ""
        return self._top_strip_serialize(self._title_desc_serialize(d))

    def to_html(self):
        b64 = base64.b64encode(self.video_bytes).decode("ascii") if self.video_bytes else ""
        title_html, desc_html = self._title_desc_html()
        return (
            f'<div class="comp video-note" data-id="{self.id}" style="left:{self.pos().x()}px;top:{self.pos().y()}px;'
            f'width:{self._w}px;height:{self._h}px;">{self._top_strip_html()}{title_html}'
            f'<video controls src="data:video/mp4;base64,{b64}"></video>{desc_html}</div>'
        )


# --------------------------------------------------------------------------
# Freehand drawing
# --------------------------------------------------------------------------

class DrawingItem(BaseComponentItem):
    TYPE_NAME = "drawing"

    def __init__(self, x=0, y=0, w=100, h=100, strokes=None, item_id=None, allow_board_card=False):
        super().__init__(x, y, w, h, item_id)
        # See ImageItem.__init__ for why this matters for panning/zoom
        # smoothness - here it avoids rebuilding a QPainterPath from every
        # stroke's raw points on every repaint, which for a detailed
        # freehand sketch is real per-frame work. add_stroke()/
        # set_stroke_style()/set_size() all call update(), which still
        # invalidates and re-renders the cache as normal.
        self.setCacheMode(QGraphicsItem.DeviceCoordinateCache)
        self.strokes = strokes or []
        self.min_w, self.min_h = 20, 20
        # Off by default (see the "Allow to be Board Card element"
        # toolbar checkbox, shown while a drawing is selected): dragging
        # a sketch onto a Board Card rasterizes it into a flat image
        # subitem (see component_to_subitem), which most sketches aren't
        # meant for. A drawing only becomes droppable into a card once
        # this is explicitly turned on for it - see
        # MindMapScene._update_board_hover_preview / item_drag_released.
        self.allow_board_card = allow_board_card

    def add_stroke(self, color, width, points):
        self.strokes.append({"color": color, "width": width, "points": points})
        self.update()

    def set_stroke_style(self, color=None, width=None, opacity=None):
        """Restyle every stroke already in this drawing - used when the
        user selects an existing sketch and adjusts the Color/Size/Opacity
        controls in the toolbar instead of drawing something new."""
        changed = False
        for s in self.strokes:
            if color is not None:
                c = QColor(color)
                if opacity is not None:
                    c.setAlpha(max(0, min(255, int(opacity * 255))))
                else:
                    c.setAlpha(QColor(s.get("color", "#ffffff")).alpha())
                s["color"] = c.name(QColor.HexArgb)
                changed = True
            elif opacity is not None:
                c = QColor(s.get("color", "#ffffff"))
                c.setAlpha(max(0, min(255, int(opacity * 255))))
                s["color"] = c.name(QColor.HexArgb)
                changed = True
            if width is not None:
                s["width"] = max(0.5, width)
                changed = True
        if changed:
            self.update()

    def set_size(self, w, h):
        # Rescale every stroke's points (and pen width) so the drawing
        # visually scales together with its bounding box, instead of the
        # box growing/shrinking around a strokes list that stayed put.
        old_w, old_h = self._w, self._h
        new_w = max(self.min_w, w)
        new_h = max(self.min_h, h)
        sx = new_w / old_w if old_w else 1.0
        sy = new_h / old_h if old_h else 1.0
        savg = (sx + sy) / 2.0
        if sx != 1.0 or sy != 1.0:
            for s in self.strokes:
                s["points"] = [[p[0] * sx, p[1] * sy] for p in s.get("points", [])]
                s["width"] = max(0.5, s.get("width", 3) * savg)
        super().set_size(w, h)

    def paint(self, painter, option, widget=None):
        painter.setRenderHint(QPainter.Antialiasing)
        if self.isSelected():
            outline = QColor(self.color) if self.color else QColor(76, 139, 245)
            outline.setAlpha(130)
            painter.setPen(QPen(outline, 1, Qt.DashLine))
            painter.setBrush(Qt.NoBrush)
            painter.drawRect(self.rect())
        for s in self.strokes:
            pts = s.get("points", [])
            if len(pts) < 2:
                continue
            pen = QPen(QColor(s.get("color", "#ffffff")))
            pen.setWidth(max(1, int(s.get("width", 3))))
            pen.setCapStyle(Qt.RoundCap)
            pen.setJoinStyle(Qt.RoundJoin)
            painter.setPen(pen)
            path = QPainterPath()
            path.moveTo(pts[0][0], pts[0][1])
            for p in pts[1:]:
                path.lineTo(p[0], p[1])
            painter.drawPath(path)
        self.paint_handle(painter)

    def serialize(self):
        d = super().serialize()
        d["strokes"] = self.strokes
        d["allow_board_card"] = self.allow_board_card
        return d

    def to_html(self):
        svg_lines = []
        for s in self.strokes:
            pts = s.get("points", [])
            if len(pts) < 2:
                continue
            pts_str = " ".join(f"{p[0]:.1f},{p[1]:.1f}" for p in pts)
            css_color = color_to_css(s.get("color", "#ffffff"))
            svg_lines.append(
                f'<polyline points="{pts_str}" fill="none" stroke="{css_color}" '
                f'stroke-width="{s.get("width",3)}" stroke-linecap="round" stroke-linejoin="round"/>'
            )
        svg = (
            f'<svg width="{self._w}" height="{self._h}" style="overflow:visible" '
            f'xmlns="http://www.w3.org/2000/svg">{"".join(svg_lines)}</svg>'
        )
        return (
            f'<div class="comp drawing-note" data-id="{self.id}" style="left:{self.pos().x()}px;top:{self.pos().y()}px;'
            f'width:{self._w}px;height:{self._h}px;">{svg}</div>'
        )


# --------------------------------------------------------------------------
# Arrow (two draggable endpoint handles, a few head styles to choose from)
# --------------------------------------------------------------------------

class ArrowItem(BaseComponentItem):
    TYPE_NAME = "arrow"
    DEFAULT_COLOR = "#ffffff"
    STYLES = ["single", "double", "line"]
    STYLE_LABELS = {"single": "Single Arrow", "double": "Double Arrow", "line": "Plain Line"}
    LINE_STYLES = ["solid", "dashed", "dashdot"]
    LINE_STYLE_LABELS = {"solid": "Solid Line", "dashed": "Dashed Line", "dashdot": "Dash-Dot Line"}
    ENDPOINT_R = 7
    PAD = 14
    LABEL_MAX_W = 220  # label wraps and stops growing wider past this

    def __init__(self, x=0, y=0, w=160, h=90, p1=None, p2=None, color=None,
                 stroke_width=4, style="single", line_style="solid", item_id=None,
                 label="", show_label=False, label_font=None, label_color=None,
                 label_html=None, anchor1=None, anchor2=None):
        super().__init__(x, y, max(1.0, w), max(1.0, h), item_id)
        self.color = color or self.DEFAULT_COLOR
        self.stroke_width = stroke_width
        self.style = style if style in self.STYLES else "single"
        self.line_style = line_style if line_style in self.LINE_STYLES else "solid"
        self.min_w, self.min_h = 1, 1
        self.p1 = QPointF(*p1) if p1 else QPointF(self.PAD, self._h - self.PAD)
        self.p2 = QPointF(*p2) if p2 else QPointF(self._w - self.PAD, self.PAD)
        self._drag_endpoint = None  # 1, 2, or None while dragging an end
        # Anchors let an endpoint stick to (and follow) a Board Card,
        # Text Note, or media component instead of a fixed scene point.
        # Each is None or {"item": <component>, "rx": 0..1, "ry": 0..1}
        # (rx/ry are the anchor point as a fraction of the target's own
        # width/height, so it keeps tracking correctly across both moves
        # and resizes of the target - see refresh_anchors()). Raw
        # {"item_id","rx","ry"} dicts loaded from disk are held in the
        # _pending_* attrs until resolve_pending_anchors() can look up
        # the actual item objects (which may not exist yet mid-load).
        self.anchor1 = None
        self.anchor2 = None
        self._pending_anchor1 = anchor1
        self._pending_anchor2 = anchor2
        self._drag_hover_target = None

        # An optional pill-shaped label centered on the line's midpoint,
        # toggled from the context menu (see _build_context_menu /
        # _toggle_show_label). It gets the exact same Font/B/I/U/Size
        # toolbar treatment as Text Note while its text is being edited
        # (see ArrowItem.font_targets and MainWindow.on_selection_changed).
        self.show_label = bool(show_label)
        self.label_item = EditableTextItem(self)
        self.label_item.setDefaultTextColor(QColor(label_color) if label_color else QColor("#000000"))
        self.label_item.setFont(
            _font_from_dict(label_font, base_family="Segoe UI", base_size=10.0, base_bold=True)
            if label_font else QFont("Segoe UI", 10, QFont.Bold)
        )
        self.label_item.setPlainText(label)
        self.label_item.setTextInteractionFlags(Qt.NoTextInteraction)
        self.label_item.document().setDocumentMargin(5)
        if label_html:
            self.label_item.document().setHtml(label_html)
        self.label_item.setVisible(self.show_label)
        self._label_w = 0.0
        self._label_h = 0.0
        self._autosizing_label = False
        self.label_item.document().contentsChanged.connect(self._on_label_text_changed)
        self._layout_label()

    @classmethod
    def from_scene_points(cls, p1_scene, p2_scene, color=None, stroke_width=4, style="single"):
        pad = cls.PAD
        x0 = min(p1_scene.x(), p2_scene.x()) - pad
        y0 = min(p1_scene.y(), p2_scene.y()) - pad
        x1 = max(p1_scene.x(), p2_scene.x()) + pad
        y1 = max(p1_scene.y(), p2_scene.y()) + pad
        w, h = max(1.0, x1 - x0), max(1.0, y1 - y0)
        return cls(
            x0, y0, w, h,
            p1=(p1_scene.x() - x0, p1_scene.y() - y0),
            p2=(p2_scene.x() - x0, p2_scene.y() - y0),
            color=color, stroke_width=stroke_width, style=style,
        )

    # Arrows resize by dragging their endpoints, not a corner handle.
    def handle_rect(self):
        return QRectF()

    def paint_handle(self, painter):
        pass

    def _qt_dash_style(self):
        if self.line_style == "dashed":
            return Qt.DashLine
        if self.line_style == "dashdot":
            return Qt.DashDotLine
        return Qt.SolidLine

    def _dasharray(self):
        """SVG stroke-dasharray string matching _qt_dash_style(), scaled to
        the current stroke width so thick lines don't end up with tiny
        dashes. Empty string means solid (no dasharray attribute)."""
        w = max(1.0, self.stroke_width)
        if self.line_style == "dashed":
            return f"{w * 2.5:.1f},{w * 1.5:.1f}"
        if self.line_style == "dashdot":
            return f"{w * 2.5:.1f},{w * 1.3:.1f},{w * 0.6:.1f},{w * 1.3:.1f}"
        return ""

    def _head_margin(self):
        # How far the arrowhead triangle reaches back from its tip, at
        # the current stroke width - see _arrow_head_path().
        return max(8, self.stroke_width * 3)

    def boundingRect(self):
        # The fixed PAD used when the arrow's geometry is (re)computed in
        # _sync_geometry()/from_scene_points() only accounts for a thin
        # default stroke. A thicker stroke makes the arrowhead (which
        # scales with stroke_width) reach further back from the tip than
        # that fixed padding allows, so it was being painted partly
        # outside this item's boundingRect. Qt only knows to repaint the
        # region inside boundingRect, so the part of the head sticking out
        # of it doesn't get redrawn/cleared correctly - visually this
        # looked like the arrowhead detaching from the shaft whenever the
        # Size slider made the stroke thick. Growing the margin here with
        # the head size keeps the whole head inside the bounding rect no
        # matter the stroke width.
        m = max(4, self._head_margin() * 0.6)
        rect = QRectF(-m, -m, self._w + 2 * m, self._h + 2 * m)
        label_rect = self._label_rect()
        if label_rect is not None:
            rect = rect.united(label_rect)
        # A headless anchored end (see _render_endpoints) draws its
        # shaft running into target's own center, which can sit outside
        # the box above - that box is only padded out to the *handle's*
        # position (on target's border), not all the way to its middle.
        # Union in a small margin around each such center point too, so
        # Qt actually knows to repaint/clip that stretch of shaft rather
        # than silently cutting it off.
        for anchor, which in ((self.anchor1, 1), (self.anchor2, 2)):
            if anchor is not None and not self._endpoint_has_arrowhead(which):
                target = self._live_anchor_target(anchor)
                if target is not None:
                    c = self.mapFromScene(target.sceneBoundingRect().center())
                    rect = rect.united(QRectF(c.x() - m, c.y() - m, 2 * m, 2 * m))
        return rect

    def shape(self):
        """A precise clickable/selectable outline hugging the actual
        line, arrowhead(s), endpoint handles and label - NOT the full
        rectangular boundingRect().

        QGraphicsItem's default shape() (used by Qt for both mouse hit-
        testing and rubber-band selection) just traces boundingRect().
        For a diagonal arrow that rectangle covers a large wedge of
        empty space on either side of the actual line - visually part
        of the canvas, but "on" the item as far as Qt is concerned. Two
        crossing arrows (a normal enough layout - see the board's own
        crossed arrows into "Mutated zombies"/"Mantis") end up with
        heavily overlapping boundingRects even though their visible
        lines only touch at one point, so a click anywhere in that
        shared empty wedge landed on whichever arrow Qt's stacking order
        happened to prefer (usually the one already selected and
        recently brought to front - see bring_to_front) instead of the
        line actually under the cursor. Building the real hit-test
        region from the line/heads/handles/label themselves - each
        already known precisely - fixes that: a click only lands on an
        arrow when it's genuinely near that arrow's visible ink.
        """
        tolerance = max(self.stroke_width + 10, self.ENDPOINT_R * 2.4)
        stroker = QPainterPathStroker()
        stroker.setWidth(tolerance)
        stroker.setCapStyle(Qt.RoundCap)
        stroker.setJoinStyle(Qt.RoundJoin)
        r_p1, r_p2 = self._render_endpoints()
        line_path = QPainterPath()
        line_path.moveTo(r_p1)
        line_path.lineTo(r_p2)
        path = stroker.createStroke(line_path)

        dx, dy = r_p2.x() - r_p1.x(), r_p2.y() - r_p1.y()
        length = max(0.0001, math.hypot(dx, dy))
        ux, uy = dx / length, dy / length
        if self.style in ("single", "double"):
            path.addPath(self._arrow_head_path(r_p2, ux, uy))
        if self.style == "double":
            path.addPath(self._arrow_head_path(r_p1, -ux, -uy))

        # Endpoint drag handles - only actionable while already
        # selected (see mousePressEvent/_endpoint_at), but folding them
        # into the shape unconditionally is harmless and keeps this
        # simple; they're normally already covered by the stroked line
        # above anyway.
        r = self.ENDPOINT_R * 2.4
        path.addEllipse(self.p1, r, r)
        path.addEllipse(self.p2, r, r)

        label_rect = self._label_rect()
        if label_rect is not None:
            path.addRoundedRect(label_rect, 6, 6)
        return path

    def set_stroke_width(self, width):
        """Use this (rather than setting stroke_width directly) so the
        item's cached geometry is invalidated first - required whenever
        the arrowhead's size might grow past the current boundingRect."""
        self.prepareGeometryChange()
        self.stroke_width = max(0.5, width)
        self.update()

    def _endpoint_at(self, local_pos):
        if (local_pos - self.p1).manhattanLength() <= self.ENDPOINT_R * 2.4:
            return 1
        if (local_pos - self.p2).manhattanLength() <= self.ENDPOINT_R * 2.4:
            return 2
        return None

    def mousePressEvent(self, event):
        self._raised_this_press = False
        if self.isSelected():
            idx = self._endpoint_at(event.pos())
            if idx is not None:
                self._drag_endpoint = idx
                event.accept()
                return
        self._drag_endpoint = None
        super().mousePressEvent(event)

    @staticmethod
    def _snap_to_angle(pivot, pt, step_deg=45):
        """Snap `pt` to the nearest `step_deg` increment of rotation
        around `pivot`, keeping its distance from `pivot` unchanged."""
        dx, dy = pt.x() - pivot.x(), pt.y() - pivot.y()
        dist = math.hypot(dx, dy)
        if dist < 1e-6:
            return pt
        angle = math.atan2(dy, dx)
        step = math.radians(step_deg)
        snapped = round(angle / step) * step
        return QPointF(pivot.x() + dist * math.cos(snapped), pivot.y() + dist * math.sin(snapped))

    def mouseMoveEvent(self, event):
        if self._drag_endpoint is not None:
            self._raise_to_front_if_needed()
            scene_pt = event.scenePos()
            if event.modifiers() & Qt.ControlModifier:
                # Rotate around the endpoint that is *not* being dragged,
                # snapping every 45 degrees.
                pivot = self.mapToScene(self.p2 if self._drag_endpoint == 1 else self.p1)
                scene_pt = self._snap_to_angle(pivot, scene_pt)
            target = self._find_anchor_target(scene_pt)
            self._drag_hover_target = target
            scene = self.scene()
            if scene is not None and hasattr(scene, "show_anchor_highlight"):
                scene.show_anchor_highlight(target)
            if target is not None:
                # Preview the edge point it would snap to if dropped here
                # (see _border_point) - the same center-orbit border
                # computation used to actually commit the anchor on
                # release (_set_anchor), so the preview always matches
                # exactly where the endpoint will end up.
                local_edge, _rx_ry, _side = self._border_point(target, scene_pt)
                scene_pt = target.mapToScene(local_edge)
            if self._drag_endpoint == 1:
                self._sync_geometry(scene_pt, self.mapToScene(self.p2))
            else:
                self._sync_geometry(self.mapToScene(self.p1), scene_pt)
            event.accept()
            return
        super().mouseMoveEvent(event)

    # How far outside a component's own rectangle an endpoint can still
    # be dragged and have that component detected as the anchor target
    # (see _find_anchor_target). Without this margin, only literal
    # containment counted - and since you naturally drift *into* a
    # component while approaching its bottom/right side but tend to stop
    # just *outside* it while approaching from the top/left, snapping
    # only ever seemed to work for the bottom/right edges.
    ANCHOR_HOVER_MARGIN = 40

    def _find_anchor_target(self, scene_pt):
        """Return the Board Card / Text Note / media component whose
        rectangle - expanded by ANCHOR_HOVER_MARGIN on every side -
        contains `scene_pt`, or None. Used while dragging an endpoint to
        decide what it would anchor to if dropped here.

        Among every candidate whose expanded rectangle contains
        scene_pt, picks whichever one's actual (unexpanded) rectangle is
        closest to scene_pt - not simply the topmost by z-order. Two
        components placed near each other (a common layout - see the
        board's own card row) each get their own ANCHOR_HOVER_MARGIN-
        widened hover zone, and those zones readily overlap in the gap
        between the components, especially for larger components since
        a bigger rectangle's margin band is more likely to reach a
        neighbor. Picking purely by z-order there could return whichever
        component happens to sit higher in stacking order even though
        the point is actually sitting right next to (and closer to) a
        totally different one - which looks exactly like the arrow
        snapping into a neighboring component's edge/corner instead of
        the one the user was actually pointing at. Distance-to-actual-
        rect first (falling back to z-order only for an exact tie, e.g.
        scene_pt genuinely inside more than one real rectangle at once)
        fixes that: whichever component's true border the point is
        nearest to wins, matching what the user is visually next to."""
        scene = self.scene()
        if scene is None:
            return None
        best, best_dist, best_z = None, None, None
        for it in scene.items():
            if it is self or it is self.label_item:
                continue
            if not isinstance(it, ANCHOR_TARGET_TYPES):
                continue
            rect = it.sceneBoundingRect()
            expanded = rect.adjusted(
                -self.ANCHOR_HOVER_MARGIN, -self.ANCHOR_HOVER_MARGIN,
                self.ANCHOR_HOVER_MARGIN, self.ANCHOR_HOVER_MARGIN,
            )
            if not expanded.contains(scene_pt):
                continue
            dx = max(rect.left() - scene_pt.x(), 0.0, scene_pt.x() - rect.right())
            dy = max(rect.top() - scene_pt.y(), 0.0, scene_pt.y() - rect.bottom())
            dist = math.hypot(dx, dy)
            if (best is None or dist < best_dist - 1e-6
                    or (abs(dist - best_dist) <= 1e-6 and it.zValue() > best_z)):
                best, best_dist, best_z = it, dist, it.zValue()
        return best

    @staticmethod
    def _border_point(target, scene_pt):
        """Where the ray from target's own *center* toward `scene_pt`
        crosses target's rectangle border, as both a local QPointF and
        the (rx, ry) fraction of target's width/height it corresponds
        to. This is what makes an anchored endpoint "orbit" its target:
        the returned point always faces directly toward `scene_pt`, so
        as scene_pt sweeps around target, this point continuously
        slides around target's own perimeter in lockstep with it,
        rather than jumping abruptly between edges the way a plain
        nearest-point search can (nearest-point picks whichever edge is
        closest in raw Euclidean distance, which doesn't always agree
        with which edge is actually being "faced" - most noticeably for
        a point sitting almost opposite one of target's corners).

        `scene_pt` is mapped into target's local space first, and the
        ray is cast from target's local center (w/2, h/2) through that
        point. This is an ordinary box/ray intersection: for each axis
        the ray is actually moving along, work out how far it has to
        travel before reaching *that axis's own* edge, and stop at
        whichever axis's distance is smaller - stopping at the nearer
        one is what keeps the landing point on the box's real border
        instead of overshooting past a corner. If `scene_pt` lands
        exactly on target's own center - no direction to orbit toward
        at all - this defaults to facing right.

        Used both for the live drop preview while dragging an endpoint
        and - via _set_anchor - to fix the border point an anchor sticks
        to once dropped, as well as - via _anchor_scene_point - to keep
        re-facing that point whenever the arrow's other end later moves.
        All three deliberately share this one center-relative
        computation so the preview, the drop, and every later re-orbit
        agree on exactly the same point for the same inputs."""
        w = max(1.0, target._w)
        h = max(1.0, target._h)
        local = target.mapFromScene(scene_pt)
        cx, cy = w / 2.0, h / 2.0
        dx, dy = local.x() - cx, local.y() - cy
        if abs(dx) < 1e-6 and abs(dy) < 1e-6:
            dx, dy = 1.0, 0.0
        # How far (as a multiple of (dx, dy)) the ray travels before it
        # would cross each axis's own edge line - only the axis the ray
        # actually moves along has a finite crossing at all; whichever
        # of the two is smaller is the one the ray reaches first, and
        # that's the edge the point lands on.
        t_candidates = []
        if dx > 1e-9:
            t_candidates.append((w - cx) / dx)
        elif dx < -1e-9:
            t_candidates.append((0.0 - cx) / dx)
        if dy > 1e-9:
            t_candidates.append((h - cy) / dy)
        elif dy < -1e-9:
            t_candidates.append((0.0 - cy) / dy)
        t = min(t_candidates) if t_candidates else 0.0
        lx = min(w, max(0.0, cx + dx * t))
        ly = min(h, max(0.0, cy + dy * t))
        if lx <= 1e-6:
            side = "left"
        elif lx >= w - 1e-6:
            side = "right"
        elif ly <= 1e-6:
            side = "top"
        else:
            side = "bottom"
        return QPointF(lx, ly), (lx / w, ly / h), side

    def _endpoint_has_arrowhead(self, which):
        """True if endpoint 1 or 2 actually draws an arrowhead of its
        own: p2 has one whenever the arrow has a head at all (style
        "single" or "double"), p1 only for a double-headed arrow. A
        "line" style, or the tail end of a "single" arrow, is headless -
        see _render_endpoints, which is where this distinction actually
        matters."""
        if which == 2:
            return self.style in ("single", "double")
        return self.style == "double"

    def _render_endpoints(self):
        """The local (p1, p2) pair to actually draw the shaft/head/hit-
        test outline between - which is NOT always self.p1/self.p2.

        self.p1/self.p2 double as the green drag-handle positions (see
        paint()'s isSelected() block and _endpoint_at) and, for an
        anchored end, sit exactly on target's border (see _border_point)
        - they need to stay there so the handle stays grabbable and in
        the same place the user left it, regardless of anything below.

        But a headless anchored end (the tail of a single-headed arrow,
        or either end of a Plain Line) has no arrowhead that needs a
        precise point to sit on. For that end specifically, the drawn
        shaft is instead run all the way to target's own center: since
        target's own opaque box paints over the part of the shaft that
        ends up underneath it, this reads as the line being anchored to
        the component as a whole rather than merely grazing its edge -
        while the green handle (see above) stays put on the border,
        still exactly where it's always been, still the actual anchor
        point that's saved/restored and still what you grab to detach
        it. An anchored end *with* an arrowhead is unaffected: the head
        still needs to stay visible, so it keeps stopping exactly at the
        border point returned by _border_point.

        Free (unanchored) endpoints are always returned as-is."""
        p1, p2 = self.p1, self.p2
        if self.anchor1 is not None and not self._endpoint_has_arrowhead(1):
            target = self._live_anchor_target(self.anchor1)
            if target is not None:
                p1 = self.mapFromScene(target.sceneBoundingRect().center())
        if self.anchor2 is not None and not self._endpoint_has_arrowhead(2):
            target = self._live_anchor_target(self.anchor2)
            if target is not None:
                p2 = self.mapFromScene(target.sceneBoundingRect().center())
        return p1, p2

    @staticmethod
    def _live_anchor_target(anchor):
        """Return anchor["item"] if it's still a live, in-scene
        component, or None if its target has been (or is mid-being)
        destroyed - e.g. by MindMapScene.clear_board() tearing down a
        board during navigation. `target.scene()` raises RuntimeError
        rather than returning None once the target's underlying C++
        object is actually deleted (as opposed to merely removed from
        the scene, which is what the plain "target.scene() is not
        None" check elsewhere in this class was already handling) -
        that unhandled RuntimeError, raised from inside boundingRect()/
        paint() while Qt itself is mid-repaint, is what crashed the app
        instead of just quietly rendering the arrow as if this end were
        unanchored the moment its target vanished. Every place that
        reads an anchor's target for rendering/geometry should go
        through this instead of touching anchor["item"] directly."""
        if anchor is None:
            return None
        target = anchor.get("item")
        if target is None:
            return None
        try:
            if target.scene() is None:
                return None
        except RuntimeError:
            return None
        return target

    def _effective_snap_method(self, target):
        """Resolve which method - "orbit" or "absolute" - governs an
        endpoint anchored to `target`: that component's own per-item
        override (self.arrow_snap_method, set via its context menu's
        "Arrow Snapping" submenu - see BaseComponentItem._add_arrow_snap_
        menu) if it has one, otherwise the app-wide Preferences > Default
        Arrow Snapping Method. Falls back to "orbit" (the original, only
        prior behaviour) if neither is available."""
        method = getattr(target, "arrow_snap_method", None)
        if method in ARROW_SNAP_METHODS:
            return method
        scene = self.scene()
        mw = getattr(scene, "main_window", None) if scene is not None else None
        prefs = getattr(mw, "prefs", None) if mw is not None else None
        if prefs:
            method = prefs.get("default_arrow_snap_method", "orbit")
            if method in ARROW_SNAP_METHODS:
                return method
        return "orbit"

    @staticmethod
    def _anchor_fixed_scene_point(anchor):
        """Where an "absolute"-method anchored endpoint sits: the exact
        same local (rx, ry) point on target it was originally dropped on
        (the "punkt zaczepienia" / attachment point - set once in
        _set_anchor and never re-picked afterwards for this method),
        rescaled to target's *current* width/height so it still tracks a
        move or resize. Unlike _anchor_scene_point (the "orbit" method),
        this never re-faces the arrow's other endpoint - the point simply
        stays glued to the same spot on target."""
        target = anchor["item"]
        w = max(1.0, target._w)
        h = max(1.0, target._h)
        local = QPointF(anchor["rx"] * w, anchor["ry"] * h)
        return target.mapToScene(local)

    def _set_anchor(self, endpoint, target, scene_pt):
        _local_edge, (rx, ry), side = self._border_point(target, scene_pt)
        anchor = {"item": target, "rx": rx, "ry": ry, "side": side}
        if endpoint == 1:
            self.anchor1 = anchor
        else:
            self.anchor2 = anchor

    def _anchor_scene_point(self, anchor, other_scene_pt):
        """Where an anchored endpoint sits on its target's outer border:
        the point where the ray from target's own center toward
        `other_scene_pt` (the arrow's other endpoint's actual current
        position) crosses target's rectangle, via the same
        _border_point() computation used live while dragging an
        endpoint into place - so the preview, the drop, and every later
        refresh all agree on exactly the same point for the same inputs.

        This is what makes an anchored endpoint genuinely "orbit" its
        own target: as the other end moves all the way around target,
        this point continuously slides all the way around target's
        border to keep facing it - see _border_point's own docstring for
        the actual ray/box intersection this relies on.

        anchor's rx/ry/side are updated here to whatever was just
        computed, so a saved board reloads already facing the way it
        last did live, rather than snapping back to its original drop
        edge on the next load.

        Called from refresh_anchors only when the anchor's own target is
        the item that just moved or resized (re-orbiting it to keep
        facing the arrow's other end) - never for an unrelated scene
        change, and never while the arrow's own endpoint is being
        dragged, see refresh_anchors's `mover` check."""
        target = anchor["item"]
        local_edge, (rx, ry), side = self._border_point(target, other_scene_pt)
        anchor["rx"], anchor["ry"], anchor["side"] = rx, ry, side
        return target.mapToScene(local_edge)

    def refresh_anchors(self, mover=None):
        """Recompute this arrow's geometry from whichever endpoints are
        anchored - but only actually re-pick a (possibly new) border
        point for an anchored endpoint when `mover` is that endpoint's
        own target, i.e. the component it's anchored to is what just
        moved or resized. Any other change in the scene - including the
        arrow's other, unrelated endpoint moving, or simply the direct
        call right after a manual drop in mouseReleaseEvent - leaves an
        anchored endpoint exactly where it already is instead of
        re-picking the nearest border point. Previously this recomputed
        both anchors on every single call, which meant an endpoint you
        had just manually dropped at a specific spot on its target's
        edge (see mouseReleaseEvent -> _set_anchor) got immediately
        overridden by a *different* nearest-point search (this one
        measured against the other endpoint's position rather than
        where you actually released the mouse) the moment
        refresh_anchors ran right after - visibly snapping the endpoint
        away from where it was just placed. Called by the scene (see
        MindMapScene.refresh_anchored_arrows) whenever any component
        changes, and also right after an endpoint is (dis)connected in
        mouseReleaseEvent - a no-op if neither end is anchored.

        `mover` is whichever item's move/resize triggered this call, if
        any (see BaseComponentItem._notify_arrows_moved). When that
        mover is this very arrow - i.e. the user is dragging the
        arrow's own (anchored or free) endpoint, or moving the whole
        arrow - this deliberately does nothing at all, so a drag of the
        arrow's own endpoint doesn't fight the drag by recomputing the
        very point being moved."""
        if mover is self:
            return
        if self.anchor1 is None and self.anchor2 is None:
            return
        p1_scene = self.mapToScene(self.p1)
        p2_scene = self.mapToScene(self.p2)
        changed = False
        # While the user is actively dragging one of this arrow's own
        # endpoints, leave that endpoint alone here. This method also
        # runs *reentrantly* mid-drag - moving the arrow (via the drag's
        # own _sync_geometry call) triggers setPos(), which triggers this
        # same refresh via the scene - and if the endpoint being dragged
        # is itself the anchored one, recomputing it here would instantly
        # snap it back onto the target, making it look impossible to pull
        # the anchored endpoint away at all.
        if self.anchor1 is not None and self._drag_endpoint != 1:
            target = self._live_anchor_target(self.anchor1)
            if target is None:
                self.anchor1 = None
            elif mover is target:
                if self._effective_snap_method(target) == "absolute":
                    p1_scene = self._anchor_fixed_scene_point(self.anchor1)
                else:
                    p1_scene = self._anchor_scene_point(self.anchor1, p2_scene)
                changed = True
        if self.anchor2 is not None and self._drag_endpoint != 2:
            target = self._live_anchor_target(self.anchor2)
            if target is None:
                self.anchor2 = None
            elif mover is target:
                if self._effective_snap_method(target) == "absolute":
                    p2_scene = self._anchor_fixed_scene_point(self.anchor2)
                else:
                    p2_scene = self._anchor_scene_point(self.anchor2, p1_scene)
                changed = True
        if changed:
            self._sync_geometry(p1_scene, p2_scene)

    def resolve_pending_anchors(self, id_map):
        """Turn the {"item_id","rx","ry"} dicts loaded from disk into
        real anchor1/anchor2 references - called once after every item
        in the board has been created (see MindMapScene.load), since the
        anchor's target may not have existed yet at this arrow's own
        construction time."""
        pending1 = self._pending_anchor1
        if pending1:
            target = id_map.get(pending1.get("item_id"))
            if target is not None:
                self.anchor1 = {"item": target, "rx": pending1.get("rx", 0.5), "ry": pending1.get("ry", 0.5),
                                 "side": pending1.get("side")}
        self._pending_anchor1 = None
        pending2 = self._pending_anchor2
        if pending2:
            target = id_map.get(pending2.get("item_id"))
            if target is not None:
                self.anchor2 = {"item": target, "rx": pending2.get("rx", 0.5), "ry": pending2.get("ry", 0.5),
                                 "side": pending2.get("side")}
        self._pending_anchor2 = None

    def mouseReleaseEvent(self, event):
        if self._drag_endpoint is not None:
            endpoint = self._drag_endpoint
            target = self._drag_hover_target
            scene = self.scene()
            if scene is not None and hasattr(scene, "hide_anchor_highlight"):
                scene.hide_anchor_highlight()
            if target is not None:
                self._set_anchor(endpoint, target, event.scenePos())
            elif endpoint == 1:
                self.anchor1 = None
            else:
                self.anchor2 = None
            self._drag_hover_target = None
            self._drag_endpoint = None
            self.refresh_anchors()
            # Re-band this arrow now that its anchor state may have just
            # changed - see MindMapScene.bring_to_front: an arrow only
            # tucks behind other components once at least one endpoint
            # is actually anchored, so snapping an endpoint onto a
            # target here should drop it into that band immediately
            # (and pulling the last anchor loose should bring it back
            # into the normal band), not just at creation time.
            if scene is not None and hasattr(scene, "bring_to_front"):
                scene.bring_to_front(self)
            event.accept()
            return
        super().mouseReleaseEvent(event)

    def _sync_geometry(self, p1_scene, p2_scene):
        pad = self.PAD
        x0 = min(p1_scene.x(), p2_scene.x()) - pad
        y0 = min(p1_scene.y(), p2_scene.y()) - pad
        x1 = max(p1_scene.x(), p2_scene.x()) + pad
        y1 = max(p1_scene.y(), p2_scene.y()) + pad
        self.prepareGeometryChange()
        # Update the local fields *before* setPos(). setPos() synchronously
        # triggers itemChange -> _notify_arrows_moved -> the scene's
        # anchored-arrow refresh, which includes THIS arrow (an anchored
        # endpoint always re-syncs whenever the arrow itself moves, so it
        # keeps facing its target). If p1/p2 were still their old values
        # at that point, that nested refresh would read stale local
        # points paired with the item's already-new position - a mismatch
        # that computes a bogus scene point, which showed up as the
        # anchored endpoint jumping into the middle of its target or off
        # to an unrelated spot while the other endpoint was being dragged.
        self._w = max(1.0, x1 - x0)
        self._h = max(1.0, y1 - y0)
        self.p1 = QPointF(p1_scene.x() - x0, p1_scene.y() - y0)
        self.p2 = QPointF(p2_scene.x() - x0, p2_scene.y() - y0)
        self.setPos(x0, y0)
        self._layout_label()
        self.update()
        scene = self.scene()
        if scene is not None and hasattr(scene, "update_anchor_endpoint_markers"):
            scene.update_anchor_endpoint_markers()

    def hoverMoveEvent(self, event):
        if self.isSelected() and self._endpoint_at(event.pos()) is not None:
            self.setCursor(Qt.CrossCursor)
        else:
            self.setCursor(Qt.ArrowCursor)
        QGraphicsObject.hoverMoveEvent(self, event)

    def _arrow_head_path(self, tip, dirx, diry):
        size = max(8, self.stroke_width * 3)
        angle = math.atan2(diry, dirx)
        spread = math.radians(28)
        p_left = QPointF(tip.x() - size * math.cos(angle - spread), tip.y() - size * math.sin(angle - spread))
        p_right = QPointF(tip.x() - size * math.cos(angle + spread), tip.y() - size * math.sin(angle + spread))
        path = QPainterPath()
        path.moveTo(tip)
        path.lineTo(p_left)
        path.lineTo(p_right)
        path.closeSubpath()
        return path

    def _head_back_distance(self):
        """Distance from an arrowhead's tip straight back to its flat base
        edge, measured along the shaft direction - see _arrow_head_path()
        (the base corners sit `size` away from the tip, but at `spread`
        degrees off-axis, so the *on-axis* distance is size*cos(spread))."""
        size = max(8, self.stroke_width * 3)
        return size * math.cos(math.radians(28))

    # -- label (optional text pill centered on the line) ----------------
    def _recalc_label_size(self):
        doc = self.label_item.document()
        self.label_item.setTextWidth(-1)
        natural_w = doc.idealWidth()
        if natural_w > self.LABEL_MAX_W:
            self.label_item.setTextWidth(self.LABEL_MAX_W)
        br = self.label_item.boundingRect()
        self._label_w = max(20.0, br.width())
        self._label_h = max(18.0, br.height())

    def _layout_label(self):
        """Recompute the label bubble's size to fit its current text/font
        (growing OR shrinking, same as Text Note) and re-center it on the
        line's midpoint."""
        if not self.show_label:
            return
        self._recalc_label_size()
        mid = QPointF((self.p1.x() + self.p2.x()) / 2.0, (self.p1.y() + self.p2.y()) / 2.0)
        self.label_item.setPos(mid.x() - self._label_w / 2.0, mid.y() - self._label_h / 2.0)

    def _label_rect(self):
        if not self.show_label:
            return None
        return QRectF(self.label_item.pos(), QSizeF(self._label_w, self._label_h))

    def _on_label_text_changed(self):
        """Wired to the label's contentsChanged signal, and also called
        directly as the relayout hook after a toolbar font/size change
        (see _apply_text_font) - either way, the bubble resizes to fit."""
        if self._autosizing_label:
            return
        self._autosizing_label = True
        try:
            self.prepareGeometryChange()
            self._layout_label()
        finally:
            self._autosizing_label = False
        self.update()

    def font_targets(self, editing_item=None):
        return [self.label_item]

    def _toggle_show_label(self):
        self.prepareGeometryChange()
        self.show_label = not self.show_label
        if self.show_label and not self.label_item.toPlainText().strip():
            self.label_item.setPlainText("Label")
        self.label_item.setVisible(self.show_label)
        self._layout_label()
        self.update()

    def paint(self, painter, option, widget=None):
        painter.setRenderHint(QPainter.Antialiasing)
        col = QColor(self.color) if self.color else QColor(self.DEFAULT_COLOR)
        pen = QPen(col)
        pen.setWidthF(max(1, self.stroke_width))
        pen.setCapStyle(Qt.SquareCap)
        pen.setStyle(self._qt_dash_style())
        painter.setPen(pen)

        r_p1, r_p2 = self._render_endpoints()
        dx, dy = r_p2.x() - r_p1.x(), r_p2.y() - r_p1.y()
        length = max(0.0001, math.hypot(dx, dy))
        ux, uy = dx / length, dy / length

        # The shaft is drawn with a round cap, which is a full circle of
        # radius stroke_width/2 centered exactly on its endpoint. Drawing
        # that endpoint all the way out at the arrowhead's tip put the
        # round cap's curve past the head's sharp point, so the tip
        # rendered as a blunt/rounded blob instead of coming to a point.
        # Pulling the shaft's end back to the head's flat base edge (and
        # letting the solid triangle cover the rest) keeps the point sharp
        # at any stroke width.
        back = self._head_back_distance()
        line_p1, line_p2 = r_p1, r_p2
        if self.style == "double":
            b = min(back, length * 0.45)
            line_p1 = QPointF(r_p1.x() + ux * b, r_p1.y() + uy * b)
            line_p2 = QPointF(r_p2.x() - ux * b, r_p2.y() - uy * b)
        elif self.style == "single":
            b = min(back, length * 0.9)
            line_p2 = QPointF(r_p2.x() - ux * b, r_p2.y() - uy * b)
        painter.drawLine(line_p1, line_p2)

        painter.setBrush(col)
        painter.setPen(Qt.NoPen)
        if self.style in ("single", "double"):
            painter.drawPath(self._arrow_head_path(r_p2, ux, uy))
        if self.style == "double":
            painter.drawPath(self._arrow_head_path(r_p1, -ux, -uy))

        if self.isSelected():
            # Anchored endpoints are drawn differently from free ones (a
            # green core plus an outer ring, vs. plain blue) so it's
            # obvious at a glance which end is stuck to a component - and
            # therefore that dragging it away is how you detach it. With
            # both endpoints looking identical there was no visual cue
            # that an anchor existed at all.
            for pt, anchor in ((self.p1, self.anchor1), (self.p2, self.anchor2)):
                if anchor is not None:
                    painter.setPen(QPen(QColor("#ffffff"), 2))
                    painter.setBrush(QColor("#34c759"))
                    painter.drawEllipse(pt, self.ENDPOINT_R, self.ENDPOINT_R)
                    painter.setPen(QPen(QColor("#34c759"), 1.5))
                    painter.setBrush(Qt.NoBrush)
                    painter.drawEllipse(pt, self.ENDPOINT_R + 3, self.ENDPOINT_R + 3)
                else:
                    painter.setPen(QPen(QColor("#4c8bf5"), 1.5))
                    painter.setBrush(QColor("#4c8bf5"))
                    painter.drawEllipse(pt, self.ENDPOINT_R, self.ENDPOINT_R)

        label_rect = self._label_rect()
        if label_rect is not None:
            # Painted last (on top of the shaft/heads) and opaque, so the
            # line visually passes "behind" the label the same way it
            # does in a diagram tool. Uses the arrow's own color so the
            # pill always matches the line/head it's attached to.
            path = QPainterPath()
            path.addRoundedRect(label_rect, 6, 6)
            painter.setPen(QPen(QColor(0, 0, 0, 70), 1))
            painter.setBrush(col)
            painter.drawPath(path)

    def mouseDoubleClickEvent(self, event):
        label_rect = self._label_rect()
        if label_rect is not None and label_rect.contains(event.pos()):
            self.label_item.setTextInteractionFlags(Qt.TextEditorInteraction)
            self.label_item.setFocus()
            event.accept()
            return
        super().mouseDoubleClickEvent(event)

    def _build_context_menu(self, menu):
        self._style_actions = {}
        style_menu = menu.addMenu("Arrow Style")
        for st in self.STYLES:
            act = style_menu.addAction(self.STYLE_LABELS[st])
            act.setCheckable(True)
            act.setChecked(self.style == st)
            self._style_actions[act] = st
        self._line_style_actions = {}
        line_menu = menu.addMenu("Line Style")
        for ls in self.LINE_STYLES:
            act = line_menu.addAction(self.LINE_STYLE_LABELS[ls])
            act.setCheckable(True)
            act.setChecked(self.line_style == ls)
            self._line_style_actions[act] = ls
        self._label_action = menu.addAction("Show Label")
        self._label_action.setCheckable(True)
        self._label_action.setChecked(self.show_label)
        menu.addSeparator()

    def _handle_context_action(self, action):
        if action in getattr(self, "_style_actions", {}):
            self.style = self._style_actions[action]
            self.update()
        elif action in getattr(self, "_line_style_actions", {}):
            self.line_style = self._line_style_actions[action]
            self.update()
        elif action is getattr(self, "_label_action", None):
            self._toggle_show_label()

    def serialize(self):
        d = super().serialize()
        d["p1"] = [self.p1.x(), self.p1.y()]
        d["p2"] = [self.p2.x(), self.p2.y()]
        d["stroke_width"] = self.stroke_width
        d["style"] = self.style
        d["line_style"] = self.line_style
        d["label"] = self.label_item.toPlainText()
        d["show_label"] = self.show_label
        d["label_font"] = _font_to_dict(self.label_item.font())
        d["label_color"] = self.label_item.defaultTextColor().name()
        d["label_html"] = self.label_item.document().toHtml()
        d["anchor1"] = (
            {"item_id": self.anchor1["item"].id, "rx": self.anchor1["rx"], "ry": self.anchor1["ry"],
             "side": self.anchor1.get("side")}
            if self.anchor1 else None
        )
        d["anchor2"] = (
            {"item_id": self.anchor2["item"].id, "rx": self.anchor2["rx"], "ry": self.anchor2["ry"],
             "side": self.anchor2.get("side")}
            if self.anchor2 else None
        )
        return d

    def to_html(self):
        css_color = color_to_css(self.color)
        r_p1, r_p2 = self._render_endpoints()
        dx, dy = r_p2.x() - r_p1.x(), r_p2.y() - r_p1.y()
        length = max(0.0001, math.hypot(dx, dy))
        ux, uy = dx / length, dy / length
        size = max(8, self.stroke_width * 3)
        spread = math.radians(28)

        def head_polygon(tip_x, tip_y, dirx, diry):
            angle = math.atan2(diry, dirx)
            lx = tip_x - size * math.cos(angle - spread)
            ly = tip_y - size * math.sin(angle - spread)
            rx = tip_x - size * math.cos(angle + spread)
            ry = tip_y - size * math.sin(angle + spread)
            return f"{tip_x:.1f},{tip_y:.1f} {lx:.1f},{ly:.1f} {rx:.1f},{ry:.1f}"

        # Same fix as paint(): pull the shaft's endpoint back to the head's
        # flat base edge so the round line-cap doesn't blunt the tip.
        back = size * math.cos(spread)
        line_p1x, line_p1y = r_p1.x(), r_p1.y()
        line_p2x, line_p2y = r_p2.x(), r_p2.y()
        if self.style == "double":
            b = min(back, length * 0.45)
            line_p1x, line_p1y = r_p1.x() + ux * b, r_p1.y() + uy * b
            line_p2x, line_p2y = r_p2.x() - ux * b, r_p2.y() - uy * b
        elif self.style == "single":
            b = min(back, length * 0.9)
            line_p2x, line_p2y = r_p2.x() - ux * b, r_p2.y() - uy * b

        heads = []
        if self.style in ("single", "double"):
            heads.append(f'<polygon points="{head_polygon(r_p2.x(), r_p2.y(), ux, uy)}" fill="{css_color}"/>')
        if self.style == "double":
            heads.append(f'<polygon points="{head_polygon(r_p1.x(), r_p1.y(), -ux, -uy)}" fill="{css_color}"/>')
        dash = self._dasharray()
        dash_attr = f' stroke-dasharray="{dash}"' if dash else ""
        svg = (
            f'<svg width="{self._w}" height="{self._h}" style="overflow:visible" '
            f'xmlns="http://www.w3.org/2000/svg">'
            f'<line x1="{line_p1x:.1f}" y1="{line_p1y:.1f}" x2="{line_p2x:.1f}" y2="{line_p2y:.1f}" '
            f'stroke="{css_color}" stroke-width="{self.stroke_width}" stroke-linecap="square"{dash_attr}/>'
            f'{"".join(heads)}</svg>'
        )
        label_html = ""
        if self.show_label and self.label_item.toPlainText().strip():
            lf = self.label_item.font()
            # Walk the label's actual per-character formatting (same
            # helper TextNoteItem.to_html uses) so highlight/color/bold/
            # italic/underline runs applied via the toolbar survive the
            # export - label_item is a live QGraphicsTextItem, so its
            # document is always current here.
            text = _qtextdocument_to_web_html(
                self.label_item.document(), base_family=lf.family(), base_size=lf.pointSizeF())
            mid_x = (self.p1.x() + self.p2.x()) / 2.0
            mid_y = (self.p1.y() + self.p2.y()) / 2.0
            label_style_bits = [
                f"font-family:'{lf.family()}',sans-serif",
                # pointSizeF() is a point size, not a pixel size - tagging
                # it "px" here made every exported label render ~25%
                # smaller than in the app (1pt = 1.33px at the standard
                # 96 DPI most desktops/browsers assume). "pt" is a real
                # CSS unit and keeps the two in sync.
                f"font-size:{lf.pointSizeF():.1f}pt",
            ]
            if lf.bold():
                label_style_bits.append("font-weight:bold")
            if lf.italic():
                label_style_bits.append("font-style:italic")
            if lf.underline():
                label_style_bits.append("text-decoration:underline")
            label_font_style = ";".join(label_style_bits)
            label_html = (
                f'<div class="arrow-label" style="position:absolute;left:{mid_x}px;top:{mid_y}px;'
                f'transform:translate(-50%,-50%);background:{css_color};'
                f'color:{color_to_css(self.label_item.defaultTextColor().name())};'
                f'padding:5px;border-radius:6px;{label_font_style};white-space:nowrap;">'
                f'{text}</div>'
            )
        return (
            f'<div class="comp arrow-note" data-id="{self.id}" style="left:{self.pos().x()}px;'
            f'top:{self.pos().y()}px;width:{self._w}px;height:{self._h}px;">{svg}{label_html}</div>'
        )


# --------------------------------------------------------------------------
# Table (grid of editable text cells, with its own settings dialog for
# row/column count and per-role coloring)
# --------------------------------------------------------------------------

class TableSettingsDialog(QDialog):
    """Table's own edit window: row/column count plus every color role
    (header background/text, default text, and separate background/text
    colors for even and odd body rows). Opened either from the toolbar's
    Color button while a table is selected, or from the table's own
    context menu ("Change Color..."/"Table Settings...") - see
    TableItem._open_color_dialog and MainWindow.pick_color."""

    # (attribute name on TableItem, label shown in the dialog)
    COLOR_ROLES = [
        ("header_bg", "Header color"),
        ("header_text_color", "Header text color"),
        ("text_color", "Text color (default)"),
        ("odd_row_bg", "Odd row color"),
        ("odd_row_text_color", "Text color for odd rows"),
        ("even_row_bg", "Even row color"),
        ("even_row_text_color", "Text color for even rows"),
        ("grid_line_color", "Grid line color"),
    ]

    # Roles whose color dialog should let the user pick transparency too -
    # just the grid line for now, since it defaults to semi-transparent
    # white so it reads against every row/header background at once (see
    # TableItem.DEFAULT_GRID_LINE_COLOR).
    ALPHA_ROLES = {"grid_line_color"}

    def __init__(self, table_item, parent=None):
        super().__init__(parent)
        self.table_item = table_item
        self.setWindowTitle("Table Settings")
        self._colors = {name: QColor(getattr(table_item, name)) for name, _ in self.COLOR_ROLES}
        self._swatches = {}

        layout = QVBoxLayout(self)
        form = QFormLayout()
        form.setLabelAlignment(Qt.AlignLeft)

        self.rows_spin = QSpinBox()
        self.rows_spin.setRange(1, 100)
        self.rows_spin.setValue(table_item.rows)
        form.addRow("Rows:", self.rows_spin)

        self.cols_spin = QSpinBox()
        self.cols_spin.setRange(1, 26)
        self.cols_spin.setValue(table_item.cols)
        form.addRow("Columns:", self.cols_spin)

        self.grid_width_spin = QSpinBox()
        self.grid_width_spin.setRange(0, 10)
        self.grid_width_spin.setValue(table_item.grid_line_width)
        self.grid_width_spin.setSuffix(" px")
        form.addRow("Grid line width:", self.grid_width_spin)

        layout.addLayout(form)

        grid = QGridLayout()
        for i, (name, label) in enumerate(self.COLOR_ROLES):
            grid.addWidget(QLabel(label + ":"), i, 0)
            btn = QPushButton()
            btn.setFixedSize(28, 28)
            btn.clicked.connect(lambda checked=False, n=name: self._pick(n))
            self._swatches[name] = btn
            self._refresh_swatch(name)
            grid.addWidget(btn, i, 1)
        layout.addLayout(grid)

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        layout.addWidget(buttons)

    def _refresh_swatch(self, name):
        col = self._colors[name]
        # rgba(...) so the swatch itself previews the actual transparency
        # for roles like grid_line_color, instead of showing it opaque.
        self._swatches[name].setStyleSheet(
            f"background-color:rgba({col.red()},{col.green()},{col.blue()},{col.alphaF():.2f}); "
            f"border:1px solid #888;"
        )

    def _pick(self, name):
        options = QColorDialog.ShowAlphaChannel if name in self.ALPHA_ROLES else QColorDialog.ColorDialogOptions()
        chosen = QColorDialog.getColor(self._colors[name], self, "Pick color", options=options)
        if chosen.isValid():
            self._colors[name] = chosen
            self._refresh_swatch(name)

    def apply_to_table(self):
        self.table_item.set_grid_size(self.rows_spin.value(), self.cols_spin.value())
        self.table_item.set_colors(
            grid_line_width=self.grid_width_spin.value(),
            **{
                name: (col.name(QColor.HexArgb) if col.alpha() < 255 else col.name())
                for name, col in self._colors.items()
            }
        )


class TableItem(BaseComponentItem):
    """A simple editable grid: a header row plus N data rows. Each cell is
    a real EditableTextItem child - the same in-place editing widget used
    by TextNoteItem - so double-clicking a cell edits it directly with a
    text cursor exactly like a normal text component, rather than through
    a popup dialog. All the structural/styling controls (row and column
    counts, and every color role) live in TableSettingsDialog instead,
    opened via the Color button or the context menu."""

    TYPE_NAME = "table"
    DEFAULT_COLOR = "#33465e"  # unused for rendering - just gives the
                                # toolbar's Color swatch something sane to
                                # show while a table is the selection.

    DEFAULT_HEADER_BG = "#33465e"
    DEFAULT_HEADER_TEXT = "#ffffff"
    DEFAULT_TEXT_COLOR = "#e8e8e8"
    DEFAULT_EVEN_ROW_BG = "#242424"
    DEFAULT_ODD_ROW_BG = "#1b1b1b"
    # Semi-transparent white by default, since it needs to read clearly
    # against every row/header background above, which are all dark -
    # see TableSettingsDialog.COLOR_ROLES for where this is user-editable.
    DEFAULT_GRID_LINE_COLOR = "#46ffffff"
    DEFAULT_GRID_LINE_WIDTH = 1

    CELL_PAD = 6

    def __init__(self, x=0, y=0, w=360, h=200, rows=3, cols=3, item_id=None,
                 data=None, headers=None, header_bg=None, header_text_color=None,
                 text_color=None, even_row_bg=None, odd_row_bg=None,
                 even_row_text_color=None, odd_row_text_color=None,
                 header_fonts=None, data_fonts=None, header_htmls=None, data_htmls=None,
                 grid_line_color=None, grid_line_width=None):
        super().__init__(x, y, w, h, item_id)
        # See ImageItem.__init__ for why this matters for panning/zoom
        # smoothness. update() (row/col edits, restyle, resize) still
        # invalidates and re-renders the cache as normal.
        self.setCacheMode(QGraphicsItem.DeviceCoordinateCache)
        self.rows = max(1, int(rows))
        self.cols = max(1, int(cols))

        # Colors must be set before the cell text items are built below,
        # since each item's initial defaultTextColor()/bold comes from them.
        self.header_bg = header_bg or self.DEFAULT_HEADER_BG
        self.header_text_color = header_text_color or self.DEFAULT_HEADER_TEXT
        self.text_color = text_color or self.DEFAULT_TEXT_COLOR
        self.even_row_bg = even_row_bg or self.DEFAULT_EVEN_ROW_BG
        self.odd_row_bg = odd_row_bg or self.DEFAULT_ODD_ROW_BG
        self.even_row_text_color = even_row_text_color or self.text_color
        self.odd_row_text_color = odd_row_text_color or self.text_color
        self.grid_line_color = grid_line_color or self.DEFAULT_GRID_LINE_COLOR
        self.grid_line_width = self.DEFAULT_GRID_LINE_WIDTH if grid_line_width is None else grid_line_width

        init_headers = list(headers) if headers else [f"Header {c + 1}" for c in range(self.cols)]
        init_headers = (init_headers + [""] * self.cols)[:self.cols]
        init_data = [list(r) for r in data] if data else [["" for _ in range(self.cols)] for _ in range(self.rows)]
        init_data = [(list(row) + [""] * self.cols)[:self.cols] for row in init_data]
        init_data = (init_data + [["" for _ in range(self.cols)] for _ in range(self.rows)])[:self.rows]

        # Per-cell font overrides (family/size/bold/italic/underline), set
        # via the toolbar's Font/B/I/U/Size controls exactly like Text
        # Note - see font_targets()/_apply_text_font. None means "use the
        # cell's default look" (bold for headers, regular otherwise).
        init_header_fonts = list(header_fonts) if header_fonts else [None] * self.cols
        init_header_fonts = (init_header_fonts + [None] * self.cols)[:self.cols]
        init_data_fonts = [list(r) for r in data_fonts] if data_fonts else [[None] * self.cols for _ in range(self.rows)]
        init_data_fonts = [(list(row) + [None] * self.cols)[:self.cols] for row in init_data_fonts]
        init_data_fonts = (init_data_fonts + [[None] * self.cols for _ in range(self.rows)])[:self.rows]

        # Full rich-text fidelity (per-character bold/italic/underline/
        # color/highlight runs) for each cell - mirrors the plain
        # "headers"/"data" fields above, see serialize()/to_html().
        init_header_htmls = list(header_htmls) if header_htmls else [None] * self.cols
        init_header_htmls = (init_header_htmls + [None] * self.cols)[:self.cols]
        init_data_htmls = [list(r) for r in data_htmls] if data_htmls else [[None] * self.cols for _ in range(self.rows)]
        init_data_htmls = [(list(row) + [None] * self.cols)[:self.cols] for row in init_data_htmls]
        init_data_htmls = (init_data_htmls + [[None] * self.cols for _ in range(self.rows)])[:self.rows]

        # Per-row/header heights auto-grow to fit their content, the same
        # way TextNoteItem grows to fit typed text - see
        # _on_cell_text_changed / _recalc_row_heights. _grid_ready guards
        # against the contentsChanged signal firing while _header_items /
        # _cell_items are still being built (setPlainText below fires it
        # immediately).
        self._grid_ready = False
        self._header_h = 26.0
        self._row_heights = []

        self._header_items = []
        self._cell_items = []
        self._build_grid_items(init_headers, init_data, init_header_fonts, init_data_fonts,
                                init_header_htmls, init_data_htmls)
        self._update_min_size()

    # -- grid content (child EditableTextItems are the source of truth) --
    def _make_cell_item(self, text, color, bold=False, font_info=None, html=None):
        it = EditableTextItem(self)
        it.setTextInteractionFlags(Qt.NoTextInteraction)
        f = _font_from_dict(font_info, base_bold=bold) if font_info else QFont("Segoe UI", 10)
        if not font_info:
            f.setBold(bold)
        it.setFont(f)
        it.setDefaultTextColor(QColor(color))
        it.setPlainText(text)
        if html:
            it.document().setHtml(html)
        it.setZValue(1)
        it.document().contentsChanged.connect(self._on_cell_text_changed)
        return it

    def _clear_grid_items(self):
        for item in self._header_items:
            if item.scene():
                item.scene().removeItem(item)
        for row in self._cell_items:
            for item in row:
                if item.scene():
                    item.scene().removeItem(item)
        self._header_items = []
        self._cell_items = []

    def _build_grid_items(self, headers_text, data_text, header_fonts=None, data_fonts=None,
                           header_htmls=None, data_htmls=None):
        self._grid_ready = False
        header_fonts = header_fonts or [None] * self.cols
        header_htmls = header_htmls or [None] * self.cols
        self._header_items = [
            self._make_cell_item(headers_text[c], self.header_text_color, bold=True,
                                  font_info=header_fonts[c] if c < len(header_fonts) else None,
                                  html=header_htmls[c] if c < len(header_htmls) else None)
            for c in range(self.cols)
        ]
        self._cell_items = []
        data_fonts = data_fonts or [[None] * self.cols for _ in range(self.rows)]
        data_htmls = data_htmls or [[None] * self.cols for _ in range(self.rows)]
        for r in range(self.rows):
            is_even = (r + 1) % 2 == 0
            row_color = self.even_row_text_color if is_even else self.odd_row_text_color
            row_fonts = data_fonts[r] if r < len(data_fonts) else [None] * self.cols
            row_htmls = data_htmls[r] if r < len(data_htmls) else [None] * self.cols
            self._cell_items.append(
                [self._make_cell_item(data_text[r][c], row_color,
                                       font_info=row_fonts[c] if c < len(row_fonts) else None,
                                       html=row_htmls[c] if c < len(row_htmls) else None)
                 for c in range(self.cols)]
            )
        self._grid_ready = True
        self._layout_cells()

    def _current_headers(self):
        return [it.toPlainText() for it in self._header_items]

    def _current_data(self):
        return [[c.toPlainText() for c in row] for row in self._cell_items]

    def _current_header_fonts(self):
        return [_font_to_dict(it.font()) for it in self._header_items]

    def _current_data_fonts(self):
        return [[_font_to_dict(c.font()) for c in row] for row in self._cell_items]

    def _current_header_htmls(self):
        return [it.document().toHtml() for it in self._header_items]

    def _current_data_htmls(self):
        return [[c.document().toHtml() for c in row] for row in self._cell_items]

    def all_text_items(self):
        """Every editable text item in the grid - header row plus body
        cells - flattened, in reading order."""
        items = list(self._header_items)
        for row in self._cell_items:
            items.extend(row)
        return items

    def font_targets(self, editing_item=None):
        """What the toolbar's Font/B/I/U/Size controls should restyle:
        just the one cell being actively edited (double-clicked into), if
        any, otherwise every cell in the table - so selecting the whole
        table and picking a font restyles it entirely, the same way it
        restyles a whole Text Note."""
        if editing_item is not None and editing_item in self.all_text_items():
            return [editing_item]
        return self.all_text_items()

    def _update_min_size(self):
        self.min_w = max(80, self.cols * 50)
        self.min_h = max(60, (self.rows + 1) * 26)
        if self._w < self.min_w or self._h < self.min_h:
            self.prepareGeometryChange()
            self._w = max(self._w, self.min_w)
            self._h = max(self._h, self.min_h)
        # Re-derive row/header heights for the (possibly just-changed)
        # dimensions, growing self._h further still if the current
        # content needs more room than min_h alone guarantees.
        self._layout_cells()

    def set_grid_size(self, rows, cols):
        old_headers = self._current_headers()
        old_data = self._current_data()
        old_header_fonts = self._current_header_fonts()
        old_data_fonts = self._current_data_fonts()
        old_header_htmls = self._current_header_htmls()
        old_data_htmls = self._current_data_htmls()
        self.prepareGeometryChange()
        self.rows = max(1, int(rows))
        self.cols = max(1, int(cols))
        new_headers = (old_headers + [""] * self.cols)[:self.cols]
        new_header_fonts = (old_header_fonts + [None] * self.cols)[:self.cols]
        new_header_htmls = (old_header_htmls + [None] * self.cols)[:self.cols]
        new_data = []
        new_data_fonts = []
        new_data_htmls = []
        for r in range(self.rows):
            row = old_data[r] if r < len(old_data) else []
            row = (list(row) + [""] * self.cols)[:self.cols]
            new_data.append(row)
            row_fonts = old_data_fonts[r] if r < len(old_data_fonts) else []
            row_fonts = (list(row_fonts) + [None] * self.cols)[:self.cols]
            new_data_fonts.append(row_fonts)
            row_htmls = old_data_htmls[r] if r < len(old_data_htmls) else []
            row_htmls = (list(row_htmls) + [None] * self.cols)[:self.cols]
            new_data_htmls.append(row_htmls)
        self._clear_grid_items()
        self._build_grid_items(new_headers, new_data, new_header_fonts, new_data_fonts,
                                new_header_htmls, new_data_htmls)
        self._update_min_size()
        self.update()

    def set_colors(self, header_bg=None, header_text_color=None, text_color=None,
                    even_row_bg=None, odd_row_bg=None, even_row_text_color=None,
                    odd_row_text_color=None, grid_line_color=None, grid_line_width=None):
        if header_bg is not None:
            self.header_bg = header_bg
        if header_text_color is not None:
            self.header_text_color = header_text_color
        if text_color is not None:
            self.text_color = text_color
        if even_row_bg is not None:
            self.even_row_bg = even_row_bg
        if odd_row_bg is not None:
            self.odd_row_bg = odd_row_bg
        if even_row_text_color is not None:
            self.even_row_text_color = even_row_text_color
        if odd_row_text_color is not None:
            self.odd_row_text_color = odd_row_text_color
        if grid_line_color is not None:
            self.grid_line_color = grid_line_color
        if grid_line_width is not None:
            self.grid_line_width = grid_line_width
        self._apply_cell_colors()
        self.update()

    def _apply_cell_colors(self):
        for item in self._header_items:
            item.setDefaultTextColor(QColor(self.header_text_color))
        for r, row in enumerate(self._cell_items):
            is_even = (r + 1) % 2 == 0
            color = self.even_row_text_color if is_even else self.odd_row_text_color
            for item in row:
                item.setDefaultTextColor(QColor(color))

    def set_color(self, color):
        # TableItem has no single "color" - this only exists so that a
        # mixed selection (e.g. table + image, both restyled together via
        # the toolbar's Color button) doesn't crash. It nudges the header
        # background, which is the closest analog to "this item's color".
        self.header_bg = color.name() if isinstance(color, QColor) else color
        self.update()

    # -- layout geometry --------------------------------------------------
    # Rows (and the header) no longer share one uniform height. Each row's
    # height is content-driven - like TextNoteItem, it auto-grows to fit
    # its tallest cell's wrapped text and never shrinks back on its own -
    # with any leftover space (e.g. after a manual handle-resize) split
    # evenly across the header and every row.
    def _col_width(self):
        return self._w / self.cols

    def _row_min_content_h(self, items):
        """Smallest height that fits every item's current wrapped text."""
        best = 0.0
        for it in items:
            best = max(best, it.document().size().height())
        return max(26.0, best + 6.0)

    def _apply_text_widths(self):
        col_w = self._col_width()
        pad = self.CELL_PAD
        width = max(10, col_w - 2 * pad)
        for item in self._header_items:
            item.setTextWidth(width)
        for row in self._cell_items:
            for item in row:
                item.setTextWidth(width)

    def _recalc_row_heights(self, target_h=None):
        if target_h is None:
            target_h = self._h
        header_min = self._row_min_content_h(self._header_items) if self._header_items else 26.0
        if self._cell_items:
            row_mins = [self._row_min_content_h(row) for row in self._cell_items]
        else:
            row_mins = [26.0] * self.rows
        total_min = header_min + sum(row_mins)
        if target_h < total_min:
            target_h = total_min
        n_slots = 1 + self.rows
        extra = max(0.0, target_h - total_min)
        per_slot = extra / n_slots if n_slots else 0.0
        self._header_h = header_min + per_slot
        self._row_heights = [m + per_slot for m in row_mins]
        new_total = self._header_h + sum(self._row_heights)
        if abs(new_total - self._h) > 0.01:
            self.prepareGeometryChange()
            self._h = new_total

    def _position_cells(self):
        col_w = self._col_width()
        pad = self.CELL_PAD
        for c, item in enumerate(self._header_items):
            item.setPos(c * col_w + pad, 2)
        y = self._header_h
        for r, row_items in enumerate(self._cell_items):
            for c, item in enumerate(row_items):
                item.setPos(c * col_w + pad, y + 2)
            if r < len(self._row_heights):
                y += self._row_heights[r]

    def _layout_cells(self):
        if not getattr(self, "_grid_ready", False):
            return
        self._apply_text_widths()
        self._recalc_row_heights()
        self._position_cells()

    def on_resized(self):
        self._layout_cells()

    def _on_cell_text_changed(self):
        # Reflow row heights whenever a cell's text changes - not only
        # when the table as a whole needs to grow. Growing the total only
        # when total_min exceeds self._h isn't enough on its own: the
        # extra space from a resize may already be sitting unused in a
        # different row, so the row that just grew needs a *redistribution*
        # of existing height too, not just a chance to grow the total.
        # _recalc_row_heights (called via _layout_cells) handles both:
        # it grows self._h when content no longer fits, and otherwise
        # reshuffles any slack evenly - the same "grow on demand, never
        # auto-shrink" rule TextNoteItem uses, since row minimums only
        # ever come from current content and are never lowered here.
        if not getattr(self, "_grid_ready", False):
            return
        self._layout_cells()
        self.update()

    def _row_heights_or_default(self):
        return self._row_heights if self._row_heights else [26.0] * self.rows

    def _cell_at(self, pos):
        """Return ("header", col) or ("body", row, col) for a point in
        item-local coordinates, clamped to the grid bounds."""
        col_w = self._col_width()
        col = int(pos.x() // col_w) if col_w > 0 else 0
        col = max(0, min(self.cols - 1, col))
        if pos.y() <= self._header_h:
            return ("header", col)
        acc = self._header_h
        row_heights = self._row_heights_or_default()
        for r, h in enumerate(row_heights):
            acc += h
            if pos.y() <= acc or r == len(row_heights) - 1:
                return ("body", r, col)
        return ("body", self.rows - 1, col)

    # -- editing ----------------------------------------------------------
    def mouseDoubleClickEvent(self, event):
        cell = self._cell_at(event.pos())
        if cell[0] == "header":
            item = self._header_items[cell[1]]
        else:
            _, row, col = cell
            item = self._cell_items[row][col]
        item.setTextInteractionFlags(Qt.TextEditorInteraction)
        item.setFocus()
        local_pos = event.pos() - item.pos()
        doc_pos = item.document().documentLayout().hitTest(local_pos, Qt.FuzzyHit)
        cursor = item.textCursor()
        if doc_pos >= 0:
            cursor.setPosition(doc_pos)
        else:
            cursor.movePosition(QTextCursor.End)
        item.setTextCursor(cursor)
        event.accept()
        super().mouseDoubleClickEvent(event)

    # -- painting -----------------------------------------------------
    def paint(self, painter, option, widget=None):
        painter.setRenderHint(QPainter.Antialiasing, False)
        rect = self.rect()
        col_w = self._col_width()
        row_heights = self._row_heights_or_default()

        # Header row background
        header_rect = QRectF(rect.x(), rect.y(), rect.width(), self._header_h)
        painter.setPen(Qt.NoPen)
        painter.setBrush(QColor(self.header_bg))
        painter.drawRect(header_rect)

        # Data row backgrounds (cell text itself is drawn by the child
        # EditableTextItems, positioned in _layout_cells). Row boundaries
        # are computed from each row's own (auto-grown) height rather
        # than a single uniform row height.
        y = self._header_h
        boundaries = [0.0, self._header_h]
        for r in range(self.rows):
            is_even = (r + 1) % 2 == 0  # 1-based row number, so row 2 is "even"
            row_bg = self.even_row_bg if is_even else self.odd_row_bg
            h = row_heights[r] if r < len(row_heights) else 26.0
            row_rect = QRectF(rect.x(), rect.y() + y, rect.width(), h)
            painter.setPen(Qt.NoPen)
            painter.setBrush(QColor(row_bg))
            painter.drawRect(row_rect)
            y += h
            boundaries.append(y)

        # Grid lines - color and thickness are user-editable
        # (TableSettingsDialog's "Grid line color"/"Grid line width" -
        # see self.grid_line_color/self.grid_line_width), defaulting to a
        # thin, light, semi-opaque line rather than a dark one:
        # header/row backgrounds here are all dark (#33465e/#242424/
        # #1b1b1b), so a low-alpha *black* line barely shows up against
        # them.
        if self.grid_line_width > 0:
            painter.setBrush(Qt.NoBrush)
            painter.setPen(QPen(QColor(self.grid_line_color), self.grid_line_width))
            # Round to whole pixels: row heights auto-grow to fractional
            # values (see _recalc_row_heights's per_slot math), and with
            # antialiasing off a line at e.g. y=394.37 rasterizes as a
            # blurry/uneven 1-2px smear instead of one crisp pixel line -
            # which is what made some grid lines look noticeably thicker
            # or fuzzier than others.
            for c in range(1, self.cols):
                x = round(rect.x() + c * col_w)
                painter.drawLine(QPointF(x, round(rect.y())), QPointF(x, round(rect.y() + rect.height())))
            for yb in boundaries:
                y_line = round(rect.y() + yb)
                painter.drawLine(QPointF(round(rect.x()), y_line), QPointF(round(rect.x() + rect.width()), y_line))

        # Outer frame - blue while selected, like every other component
        painter.setPen(QPen(QColor("#4c8bf5"), 2) if self.isSelected() else QPen(QColor(0, 0, 0, 120), 1))
        painter.drawRect(rect)
        self.paint_handle(painter)

    # -- color entry point (toolbar Color button / context menu) --------
    def _open_color_dialog(self):
        self.open_settings_dialog()

    def open_settings_dialog(self, parent=None):
        if parent is None:
            views = self.scene().views() if self.scene() else []
            parent = views[0] if views else None
        dlg = TableSettingsDialog(self, parent)
        if dlg.exec() == QDialog.Accepted:
            dlg.apply_to_table()

    def _build_context_menu(self, menu):
        self._table_settings_action = menu.addAction("Table Settings\u2026")
        menu.addSeparator()

    def _handle_context_action(self, action):
        if action == self._table_settings_action:
            self.open_settings_dialog()

    # -- serialization --------------------------------------------------
    def serialize(self):
        d = super().serialize()
        d["rows"] = self.rows
        d["cols"] = self.cols
        d["headers"] = self._current_headers()
        d["data"] = self._current_data()
        d["header_fonts"] = self._current_header_fonts()
        d["data_fonts"] = self._current_data_fonts()
        d["header_htmls"] = self._current_header_htmls()
        d["data_htmls"] = self._current_data_htmls()
        d["header_bg"] = self.header_bg
        d["header_text_color"] = self.header_text_color
        d["text_color"] = self.text_color
        d["even_row_bg"] = self.even_row_bg
        d["odd_row_bg"] = self.odd_row_bg
        d["even_row_text_color"] = self.even_row_text_color
        d["odd_row_text_color"] = self.odd_row_text_color
        d["grid_line_color"] = self.grid_line_color
        d["grid_line_width"] = self.grid_line_width
        return d

    def to_html(self):
        def font_style_bits(font_dict):
            bits = []
            if not font_dict:
                return bits
            fam = font_dict.get("font_family")
            if fam:
                bits.append(f"font-family:'{fam}',sans-serif")
            size = font_dict.get("font_size")
            if size:
                bits.append(f"font-size:{float(size):.1f}pt")
            if font_dict.get("bold"):
                bits.append("font-weight:bold")
            if font_dict.get("italic"):
                bits.append("font-style:italic")
            if font_dict.get("underline"):
                bits.append("text-decoration:underline")
            return bits

        def cell_rich_html(text_item, font_dict):
            # Walk the cell's actual per-character formatting (same
            # helper TextNoteItem.to_html uses) so highlight/color/bold/
            # italic/underline runs applied via the toolbar survive the
            # export - every cell is a live QGraphicsTextItem, so its
            # document is always current here.
            fam = (font_dict or {}).get("font_family") or "Segoe UI"
            size = (font_dict or {}).get("font_size") or 10.0
            return _qtextdocument_to_web_html(text_item.document(), base_family=fam, base_size=size)

        header_fonts = self._current_header_fonts()
        data_fonts = self._current_data_fonts()
        cell_border = (
            f"border:{self.grid_line_width}px solid {color_to_css(self.grid_line_color)}"
            if self.grid_line_width > 0 else "border:none"
        )
        header_cells = "".join(
            f'<th style="text-align:left;padding:6px;{cell_border};background:{color_to_css(self.header_bg)};'
            f'color:{color_to_css(self.header_text_color)};'
            f'{";".join(font_style_bits(header_fonts[c]))}">{cell_rich_html(it, header_fonts[c])}</th>'
            for c, it in enumerate(self._header_items)
        )
        body_rows = []
        for r in range(self.rows):
            is_even = (r + 1) % 2 == 0
            row_bg = self.even_row_bg if is_even else self.odd_row_bg
            row_text_color = self.even_row_text_color if is_even else self.odd_row_text_color
            cells = "".join(
                f'<td style="padding:6px;{cell_border};background:{color_to_css(row_bg)};'
                f'color:{color_to_css(row_text_color)};'
                f'{";".join(font_style_bits(data_fonts[r][c]))}">'
                f'{cell_rich_html(self._cell_items[r][c], data_fonts[r][c])}</td>'
                for c in range(self.cols)
            )
            body_rows.append(f"<tr>{cells}</tr>")
        table_html = (
            f'<table style="width:100%;height:100%;border-collapse:collapse;'
            f'font-family:\'Segoe UI\',sans-serif;">'
            f'<thead><tr>{header_cells}</tr></thead>'
            f'<tbody>{"".join(body_rows)}</tbody></table>'
        )
        return (
            f'<div class="comp table-note" data-id="{self.id}" style="left:{self.pos().x()}px;top:{self.pos().y()}px;'
            f'width:{self._w}px;height:{self._h}px;opacity:{self.opacity():.2f}">{table_html}</div>'
        )


# --------------------------------------------------------------------------
# Board card (modular Milanote-style container with sub items)
# --------------------------------------------------------------------------

class _SubitemTextEdit(EditableTextItem):
    """EditableTextItem used to edit a "text" subitem's text in place
    inside a BoardCardItem. Identical editing behavior to a normal Text
    component, plus a callback that commits the edit and tears the
    overlay down again once it loses focus."""

    def __init__(self, parent, on_finish):
        super().__init__(parent)
        self._on_finish = on_finish

    def focusOutEvent(self, event):
        super().focusOutEvent(event)
        if self._losing_focus_to_font_combo() or QApplication.activeModalWidget() is not None:
            # Same guard as EditableTextItem.focusOutEvent above: a modal
            # color/link dialog (or the font-family combo) only takes
            # focus momentarily. Ending the edit here - which commits the
            # subitem's text/html and tears the overlay down - would
            # leave nothing left for pick_color()/etc. to apply the
            # chosen color to once the dialog closes, and made it look
            # like the subitem's text edit had simply lost focus/selection.
            return
        if self._on_finish:
            self._on_finish()


class SubitemDragGhost(QGraphicsObject):
    """A small floating translucent preview shown while a board-card
    subitem is being dragged, so there is always a visible "object in
    hand" - including once the cursor has left the card and there would
    otherwise be no feedback at all."""

    def __init__(self, subitem):
        super().__init__()
        self.setZValue(99999)
        self.setAcceptedMouseButtons(Qt.NoButton)
        self.setAcceptHoverEvents(False)
        self._w, self._h = 150, 90
        self.will_detach = False
        self._pixmap = QPixmap()
        self._label = ""
        kind = subitem.get("kind")
        if kind in ("image", "gif"):
            self._pixmap = base64_to_pixmap(subitem.get("data", ""))
        elif kind == "video":
            self._label = "\u25B6 video"
        elif kind == "text":
            self._label = subitem.get("text", "")[:80]
        elif kind == "checklist":
            self._label = " \u00b7 ".join(subitem.get("items", []))[:80] or "Checklist"

    def boundingRect(self):
        return QRectF(0, -18, self._w, self._h + 18)

    def paint(self, painter, option, widget=None):
        painter.setRenderHint(QPainter.Antialiasing)
        accent = QColor("#ff6b6b") if self.will_detach else QColor("#4c8bf5")
        rect = QRectF(0, 0, self._w, self._h)
        path = QPainterPath()
        path.addRoundedRect(rect, 8, 8)
        painter.setOpacity(0.92)
        painter.setBrush(QColor("#262626"))
        painter.setPen(QPen(accent, 2))
        painter.drawPath(path)
        painter.save()
        painter.setClipPath(path)
        if not self._pixmap.isNull():
            scaled = self._pixmap.scaled(rect.size().toSize(), Qt.KeepAspectRatio, Qt.SmoothTransformation)
            px = (rect.width() - scaled.width()) / 2
            py = (rect.height() - scaled.height()) / 2
            painter.drawPixmap(int(px), int(py), scaled)
        elif self._label:
            painter.setPen(QColor("#eeeeee"))
            painter.drawText(rect.adjusted(8, 8, -8, -8), Qt.TextWordWrap, self._label)
        painter.restore()
        painter.setOpacity(1.0)
        painter.setPen(accent)
        caption = "Drop to detach" if self.will_detach else "Drop here to reorder"
        painter.drawText(QRectF(0, -18, self._w, 16), Qt.AlignHCenter | Qt.AlignVCenter, caption)


class _SubitemFontProxy:
    """Lightweight stand-in for a Board Card "text" subitem's default
    font, used by the shared _apply_text_font/_representative_font
    toolbar machinery (see BoardCardItem.font_targets) whenever that
    subitem is merely *selected* with a single click - not double-clicked
    into edit. This is what lets Font/B/I/U act on a single-click-selected
    subitem exactly like a standalone Text Note's own selected-but-not-
    editing whole-field styling, without keeping a live QGraphicsTextItem/
    QTextDocument around for every never-edited subitem (which is exactly
    what BoardCardItem's manual paint()-based rendering exists to avoid -
    see the class docstring above). Writes land straight back into the
    subitem dict, the same fields paint()/serialize()/to_html() already
    read - so they show up immediately, survive being dragged back out
    into a standalone component, and export to HTML identically."""

    def __init__(self, subitem, field):
        self._sub = subitem
        self._field = field
        # Cached on the instance, not recreated per call: PySide6 doesn't
        # keep a QTextDocument's Python wrapper alive just because a
        # QTextCursor was built from it (there's no Qt-level parent/
        # ownership relationship for a document with no parent), so
        # returning a brand-new one from document()/textCursor() every
        # call let it get garbage-collected out from under the still-in-
        # use QTextCursor the instant the call that created it returned -
        # a use-after-free that crashed the whole app. Keeping exactly
        # one QTextDocument per proxy, referenced by the proxy itself for
        # as long as it lives, fixes that.
        self._doc = None

    def font(self):
        sub = self._sub
        f = QFont(sub.get("font_family") or "Segoe UI", 10)
        f.setBold(bool(sub.get("bold")))
        f.setItalic(bool(sub.get("italic")))
        f.setUnderline(bool(sub.get("underline")))
        return f

    def setFont(self, f):
        sub = self._sub
        sub["font_family"] = f.family()
        sub["bold"] = f.bold()
        sub["italic"] = f.italic()
        sub["underline"] = f.underline()
        # A whole-field change overwrites any earlier per-character rich
        # text run formatting - the same "no selection = whole field"
        # rule _apply_run_format documents for every other text
        # component - so a stale bold/colored run from an earlier real
        # edit can't keep overriding the new font forever.
        sub.pop(f"{self._field}_html", None)

    def document(self):
        if self._doc is None:
            self._doc = QTextDocument()
        self._doc.setPlainText(self._sub.get(self._field, "") or "")
        return self._doc

    def textCursor(self):
        return QTextCursor(self.document())

    def opacity(self):
        return 1.0


class BoardCardItem(TopStripMixin, BaseComponentItem):
    TYPE_NAME = "board"
    DEFAULT_COLOR = "#2b2b2b"
    TITLE_H = 36  # default (single-line) height of the dark title bar at
                  # the top of the card - grows via _recalc_title_height
                  # when the title text wraps onto more than one line, so
                  # a two-or-more-line title never gets clipped/overlapped
                  # by the subitems laid out below it (see paint()).
    MEDIA_GAP = 18  # vertical gap between stacked image/gif/video subitems
    SUB_MEDIA_TITLE_H = 22  # title bar above an image/gif/video subitem,
                             # shown only when that subitem has a title
                             # AND its "show_title" flag is on - mirrors
                             # MediaCardMixin.TITLE_H on the standalone
                             # components these subitems came from.
    SUB_MEDIA_DESC_H = 20   # same idea for the description bar below
    VIDEO_HANDLE_H = 14  # thin dotted drag-strip above each embedded video
                          # player, mirroring VideoItem.DRAG_STRIP_H - the
                          # player widget below it consumes clicks for its
                          # own play/seek/mute controls, so reordering or
                          # dragging that subitem out needs its own grab
                          # target that isn't fighting the widget for clicks

    def __init__(self, x=0, y=0, w=280, h=320, title="New Board", subitems=None, item_id=None,
                 top_strip_enabled=False, top_strip_color=None, title_font=None, title_color=None,
                 title_html=None):
        super().__init__(x, y, w, h, item_id)
        # See ImageItem.__init__ for why this matters for panning/zoom
        # smoothness - it matters even more here, since this paint()
        # draws every image/gif/text subitem's chrome directly rather
        # than delegating to separate cached child items. update() (text
        # edits, gif frame changes, resize, selection) still invalidates
        # and re-renders the cache as normal.
        self.setCacheMode(QGraphicsItem.DeviceCoordinateCache)
        self._init_top_strip(top_strip_enabled, top_strip_color)
        self.subitems = subitems or []
        self.min_w, self.min_h = 160, 120
        self.setAcceptDrops(True)
        # Actual height reserved for the title bar - starts at TITLE_H but
        # grows (see _recalc_title_height) when the title text wraps onto
        # more than one line, mirroring TextNoteItem._title_h.
        self._title_h = self.TITLE_H
        self.title_item = EditableTextItem(self)
        self.title_item.setPos(10, 6)
        self.title_item.setFont(
            _font_from_dict(title_font, base_family="Segoe UI", base_size=12.0, base_bold=True)
            if title_font else QFont("Segoe UI", 12, QFont.Bold)
        )
        self.title_item.setDefaultTextColor(QColor(title_color) if title_color else QColor("#ffffff"))
        self.title_item.setPlainText(title)
        self.title_item.setTextInteractionFlags(Qt.NoTextInteraction)
        self.title_item.setTextWidth(max(10, w - 20))
        if title_html:
            self.title_item.document().setHtml(title_html)
        self.title_item.document().contentsChanged.connect(self._on_title_text_changed)
        self._recalc_title_height()

        # -- subitem drag-out / reorder state ---------------------------
        # Filled in during paint() so hit-testing always matches what is
        # currently on screen.
        self._subitem_rects = []      # list of (index, QRectF-in-item-coords)
        self._drag_sub_index = None   # index currently being dragged, or None
        self._drag_sub_moved = False  # did the mouse actually move past a threshold
        self._drag_sub_start_pos = QPointF()
        self._drag_sub_will_detach = False
        self._drag_ghost = None       # floating SubitemDragGhost while dragging

        # -- single-click "select this subitem" state -------------------
        # Set when a subitem is clicked (without being dragged/detached)
        # so it gets the same top-toolbar editing (Color, Font/B/I/U for
        # text subitems) a standalone component gets when simply
        # selected - as opposed to double-clicking it, which still opens
        # the in-place text editor below (_sub_edit_item). Only one
        # subitem across the whole app is ever selected this way at a
        # time - see MindMapScene.select_board_subitem/
        # clear_board_subitem_selection, which is what actually owns
        # this value (kept here too so paint()/mouse handlers on this
        # card don't need to reach back into the scene for it).
        self._selected_sub_index = None

        # -- in-place text-subitem editing state -------------------------
        self._sub_edit_item = None    # the _SubitemTextEdit overlay, while editing
        self._sub_edit_index = None   # index of the subitem being edited
        self._sub_edit_field = None   # which field is being edited: "text" (kind=="text")
                                       # or "title"/"description" (kind in image/gif/video)
        self._subitem_font = QFont()  # font used for text subitems, captured in paint()
        self._subitem_td_click_rects = {}  # idx -> (title_rect, desc_rect) in item coords,
                                            # for image/gif/video subitems - always reserved
                                            # at the top/bottom of the row (even when the bar
                                            # itself is currently collapsed because it has no
                                            # text yet) so double-clicking there can start
                                            # adding a title/description, not just editing an
                                            # existing one.

        # -- insertion preview while a component is dragged over this card
        self._insert_preview_y = None  # local y of the pending drop, or None

        # -- embedded video subitem players --------------------------------
        # Each "video" subitem gets a real VideoPlayerNode (the same
        # play/seek/mute controls, and actually-visible frames, the
        # standalone Video component has) embedded as a child item,
        # instead of the old static "\u25B6 video" placeholder that had
        # no actual playback at all. Keyed by id(subitem dict) - subitem
        # dicts keep their identity across reordering (see
        # mouseMoveEvent), so the mapping survives drag-to-reorder and is
        # only cleaned up when a subitem is actually removed (see
        # _prune_video_proxies).
        self._video_proxies = {}

        # -- embedded gif subitem animations --------------------------------
        # Each "gif" subitem gets its own QMovie so it actually animates
        # in place. Previously a gif subitem was drawn with a single
        # base64_to_pixmap() call in paint() - a static first-frame
        # snapshot with nothing ever driving a repaint - so it only ever
        # played back when dragged out into its own standalone GifItem
        # (which does own a QMovie). Keyed by id(subitem dict), same
        # lifetime rules as _video_proxies above (see _prune_gif_movies).
        self._gif_movies = {}

        # -- static rich-text render cache for un-edited subitems ---------
        # Painting a subitem's title/description/body with the actual
        # highlight/color/bold/... runs it was saved with (instead of
        # plain QPainter.drawText()) means building a small QTextDocument
        # from its stored *_html - this caches those per (id(subitem),
        # field) so paint() (called every repaint) doesn't rebuild one
        # from scratch every single frame; see _get_subitem_rich_doc.
        self._subitem_rich_doc_cache = {}

        # -- decoded pixmap cache for "image" subitems --------------------
        # paint() previously called base64_to_pixmap(item["data"]) - a
        # base64 decode + full PNG decode - from scratch on every single
        # repaint of the card, including every pan/zoom step. Unlike the
        # standalone ImageItem (which caches this), image subitems here
        # had no cache at all, making any board card containing an image
        # the single most expensive thing on the canvas to pan/zoom past.
        # Keyed by id(subitem dict), same lifetime rules as the caches
        # above (see _prune_image_pixmap_cache); the scaled-to-box pixmap
        # is cached separately per target size (see _get_or_create_image_pixmap).
        self._image_pixmap_cache = {}

        # -- scaled-to-box pixmap cache for image/gif subitems ------------
        # Even with the decoded pixmap cached above, paint() was still
        # calling pm.scaled() - a bilinear resample of a possibly large
        # photo - on every single repaint, including every pan/zoom step.
        # Cached per (id(subitem), target box size), and invalidated
        # automatically if the source pixmap's content actually changed
        # (tracked via QPixmap.cacheKey(), which changes on every new gif
        # frame) so animated gif subitems keep animating correctly.
        self._subitem_scaled_cache = {}

    def itemChange(self, change, value):
        if change == QGraphicsItem.ItemSceneHasChanged and value is None:
            # This card just left the scene (deleted, or a whole board
            # torn down by MindMapScene.clear_board() - e.g. navigating
            # to another board and back). GifItem.itemChange and
            # VideoPlayerNode.itemChange already do this for a
            # *standalone* gif/video component's own single movie/player -
            # but a BoardCardItem manages a whole dict of these per
            # embedded subitem (self._gif_movies / self._video_proxies),
            # and nothing was ever stopping *those* on scene removal.
            # Each QMovie's frameChanged is connected to a closure
            # (_get_or_create_gif_movie's _on_frame) that captures this
            # card itself and calls self.update() on every frame - so an
            # unstopped movie keeps this card (and everything it in turn
            # holds/prunes) alive and animating indefinitely, invisibly,
            # in the background. Repeatedly visiting a board with N
            # embedded gif/video subitems and navigating away without
            # this leaked N more still-running movies/players every
            # single time - the accumulating panning/zoom sluggishness
            # (see MindMapScene.clear_board's sceneRect note) as well as
            # steadily climbing memory/CPU use the longer a session ran.
            for entry in self._gif_movies.values():
                movie = entry["movie"]
                movie.stop()
                try:
                    movie.frameChanged.disconnect()
                except (RuntimeError, TypeError):
                    pass  # already disconnected / no receivers left
            self._gif_movies = {}
            for node in self._video_proxies.values():
                if getattr(node, "player", None) is not None:
                    node.player.stop()
            self._video_proxies = {}
        return super().itemChange(change, value)

    def _recalc_title_height(self):
        """Grow (or shrink back) the title bar to fit however many lines
        the title text currently wraps onto - see TextNoteItem's method
        of the same name, which this mirrors. Without this the title bar
        stayed a fixed single-line height, so a title wrapped onto two+
        lines (e.g. via a manual line break) got clipped/overlapped by
        the subitems laid out right below it."""
        doc_h = self.title_item.document().size().height()
        self._title_h = max(self.TITLE_H, doc_h + 12)

    def _on_title_text_changed(self):
        self._recalc_title_height()
        self.update()

    def on_resized(self):
        self.title_item.setTextWidth(max(10, self._w - 20))
        self._recalc_title_height()
        self.update()

    def mouseDoubleClickEvent(self, event):
        if self._selected_sub_index is not None:
            scene = self.scene()
            if scene is not None and hasattr(scene, "clear_board_subitem_selection"):
                scene.clear_board_subitem_selection()
            else:
                self._selected_sub_index = None
        if event.pos().y() < self._title_h:
            self.title_item.setTextInteractionFlags(Qt.TextEditorInteraction)
            self.title_item.setFocus()
        else:
            idx = self._subitem_index_at(event.pos())
            if idx is not None:
                kind = self.subitems[idx].get("kind")
                if kind == "text":
                    # A Text Note subitem carries its own optional title
                    # bar (see _sub_text_title_height/paint()) - clicking
                    # that bar should edit the title, exactly like it does
                    # on the standalone TextNoteItem it came from, not the
                    # body text underneath it.
                    rects = self._subitem_td_click_rects.get(idx)
                    title_rect = rects[0] if rects else None
                    if title_rect is not None and title_rect.contains(event.pos()):
                        self._begin_edit_subitem_field(idx, "title")
                    else:
                        self._begin_edit_subitem(idx)
                elif kind in ("image", "gif", "video"):
                    rects = self._subitem_td_click_rects.get(idx)
                    if rects:
                        title_rect, desc_rect = rects
                        if title_rect.contains(event.pos()):
                            self._begin_edit_subitem_field(idx, "title")
                        elif desc_rect.contains(event.pos()):
                            self._begin_edit_subitem_field(idx, "description")
        super().mouseDoubleClickEvent(event)

    # -- in-place editing of a "text" subitem ----------------------------
    def _begin_edit_subitem(self, idx):
        if idx is None or idx >= len(self.subitems):
            return
        if self.subitems[idx].get("kind") != "text":
            return
        self._end_edit_subitem()
        rect = None
        for i, r in self._subitem_rects:
            if i == idx:
                rect = r
                break
        if rect is None:
            return
        sub = self.subitems[idx]
        title_h, _ = self._sub_text_title_height(sub, max(1, rect.width()))
        edit = _SubitemTextEdit(self, on_finish=self._end_edit_subitem)
        edit.setPos(rect.x(), rect.y() + title_h)
        edit.setTextWidth(max(10, rect.width()))
        edit.setDefaultTextColor(self._subitem_text_color(sub))
        edit.setFont(self._subitem_font)
        edit.setPlainText(sub.get("text", ""))
        if sub.get("text_html"):
            edit.document().setHtml(sub["text_html"])
        edit.document().contentsChanged.connect(lambda: self._sync_subitem_text(idx))
        edit.setZValue(10)
        self._sub_edit_item = edit
        self._sub_edit_index = idx
        self._sub_edit_field = "text"
        edit.setTextInteractionFlags(Qt.TextEditorInteraction)
        edit.setFocus()
        cursor = edit.textCursor()
        cursor.select(QTextCursor.Document)
        edit.setTextCursor(cursor)
        self.update()

    def _sync_subitem_text(self, idx):
        if self._sub_edit_item is None or self._sub_edit_index != idx or idx >= len(self.subitems):
            return
        self.subitems[idx]["text"] = self._sub_edit_item.toPlainText()
        # Full rich-text fidelity (bold/italic/underline/color/highlight
        # runs from selection-based toolbar edits) - see to_html(), which
        # needs this to export the same highlight shown in the app,
        # since this subitem otherwise only exists as plain dict data.
        self.subitems[idx]["text_html"] = self._sub_edit_item.document().toHtml()
        self._autogrow_to_fit()
        self.update()

    # -- in-place editing of an image/gif/video subitem's title/description,
    # or a "text" subitem's own optional title bar (see paint()'s kind ==
    # "text" branch and _sub_text_title_height) - the same in-place editor
    # overlay is reused for all of these, just positioned/styled/keyed
    # differently.
    def _begin_edit_subitem_field(self, idx, field):
        if idx is None or idx >= len(self.subitems):
            return
        item = self.subitems[idx]
        kind = item.get("kind")
        if kind not in ("image", "gif", "video", "text"):
            return
        if kind == "text" and field != "title":
            return
        self._end_edit_subitem()
        rects = self._subitem_td_click_rects.get(idx)
        if not rects:
            return
        rect = rects[0] if field == "title" else rects[1]
        if rect is None:
            return
        edit = _SubitemTextEdit(self, on_finish=self._end_edit_subitem)
        if kind == "text":
            # A text subitem's title is drawn flush with the row (see
            # paint()), not inset like the media title/description bars.
            edit.setPos(rect.x(), rect.y())
            edit.setTextWidth(max(10, rect.width()))
            avail_w = max(1, rect.width())
            _, title_font = self._sub_text_title_height(item, avail_w)
            edit.setFont(title_font or QFont("Segoe UI", 11, QFont.Bold))
            title_color = item.get("title_color") or self._subitem_text_color(item).name()
            edit.setDefaultTextColor(QColor(title_color))
        else:
            edit.setPos(rect.x() + 6, rect.y())
            edit.setTextWidth(max(10, rect.width() - 12))
            if field == "title":
                edit.setDefaultTextColor(QColor("#ffffff"))
                edit.setFont(QFont("Segoe UI", 9, QFont.Bold))
            else:
                edit.setDefaultTextColor(QColor("#aaaaaa"))
                edit.setFont(QFont("Segoe UI", 8))
        edit.setPlainText(item.get(field, ""))
        if item.get(f"{field}_html"):
            edit.document().setHtml(item[f"{field}_html"])
        edit.document().contentsChanged.connect(lambda: self._sync_subitem_field(idx, field))
        edit.setZValue(10)
        self._sub_edit_item = edit
        self._sub_edit_index = idx
        self._sub_edit_field = field
        edit.setTextInteractionFlags(Qt.TextEditorInteraction)
        edit.setFocus()
        cursor = edit.textCursor()
        cursor.select(QTextCursor.Document)
        edit.setTextCursor(cursor)
        self.update()

    def _sync_subitem_field(self, idx, field):
        if (self._sub_edit_item is None or self._sub_edit_index != idx
                or self._sub_edit_field != field or idx >= len(self.subitems)):
            return
        self.subitems[idx][field] = self._sub_edit_item.toPlainText()
        self.subitems[idx][f"{field}_html"] = self._sub_edit_item.document().toHtml()
        self._autogrow_to_fit()
        self.update()

    def _end_edit_subitem(self):
        edit = self._sub_edit_item
        if edit is None:
            return
        idx = self._sub_edit_index
        field = self._sub_edit_field or "text"
        if idx is not None and idx < len(self.subitems):
            self.subitems[idx][field] = edit.toPlainText()
            self.subitems[idx][f"{field}_html"] = edit.document().toHtml()
        self._sub_edit_item = None
        self._sub_edit_index = None
        self._sub_edit_field = None
        edit.setParentItem(None)
        if edit.scene() is not None:
            edit.scene().removeItem(edit)
        self._autogrow_to_fit()
        self.update()

    @staticmethod
    def _subitem_text_color(item):
        """The color a "text" subitem is currently painted with - shared
        by paint() and _begin_edit_subitem() so the in-place editor
        starts out showing exactly the color that was on screen before
        double-click, instead of always resetting to the neutral
        default (see paint()'s kind == "text" branch for the full
        story on each of these cases)."""
        if item.get("link_url"):
            return QColor("#5b9dd9")
        if item.get("note_type") == "plaintext" and item.get("color"):
            return QColor(item.get("color"))
        if item.get("note_type") == "text" and item.get("text_color"):
            return QColor(item.get("text_color"))
        if not item.get("note_type") and item.get("color"):
            return QColor(item.get("color"))
        return QColor("#dddddd")

    def font_targets(self, editing_item=None):
        """What the toolbar's Font/B/I/U/Size controls should restyle:
        the card's own title while it's being edited, or the in-place
        editor overlay for a subitem (its body text, or its title/
        description) while one is active - this is how a board-card's
        title and subitems get the exact same Font/B/I/U/Size treatment
        as a standalone Text Note / media component (see
        MainWindow.on_selection_changed, which only includes this
        BoardCardItem in the toolbar's font selection while one of these
        is open). There's no meaningful "whole card" font to restyle
        otherwise, since a card can hold any number of
        differently-formatted subitems at once."""
        if editing_item is self.title_item:
            return [self.title_item]
        if editing_item is not None and editing_item is self._sub_edit_item:
            return [self._sub_edit_item]
        if editing_item is None and self._selected_sub_index is not None:
            idx = self._selected_sub_index
            if idx < len(self.subitems) and self.subitems[idx].get("kind") == "text":
                return [_SubitemFontProxy(self.subitems[idx], "text")]
        return []

    def _on_subitem_text_font_changed(self):
        """Relayout hook - see _apply_text_font's call to this whenever
        it exists on the target. Captures the font the toolbar just
        applied to the active subitem editor back into the subitem's own
        dict, the same way _sync_subitem_text/_sync_subitem_field already
        keep the plain text itself synced, so the formatting survives
        once editing ends and gets painted correctly (see paint()). A
        text subitem's own title (field == "title") keeps its own
        "title_font" entry, separate from the body text's "font_family"/
        "bold"/... fields, exactly like a standalone TextNoteItem does.
        An image/gif/video subitem's title/description each get their
        own "<field>_font" entry, mirroring MediaCardMixin's
        title_font/description_font."""
        idx = self._sub_edit_index
        edit = self._sub_edit_item
        field = self._sub_edit_field
        if edit is None or idx is None or idx >= len(self.subitems):
            return
        f = edit.font()
        sub = self.subitems[idx]
        kind = sub.get("kind")
        if kind == "text" and field == "title":
            sub["title_font"] = _font_to_dict(f)
        elif kind in ("image", "gif", "video") and field in ("title", "description"):
            sub[f"{field}_font"] = _font_to_dict(f)
        else:
            sub["font_family"] = f.family()
            sub["bold"] = f.bold()
            sub["italic"] = f.italic()
            sub["underline"] = f.underline()
        self._autogrow_to_fit()

    def add_subitem(self, subitem, index=None):
        """Add a subitem to this card. By default it's appended at the
        end; pass `index` (as computed by _subitem_insert_index()) to
        insert it between existing subitems instead."""
        if index is None or index < 0 or index > len(self.subitems):
            self.subitems.append(subitem)
        else:
            self.subitems.insert(index, subitem)
        self._autogrow_to_fit()
        self.update()

    def show_insert_preview(self, local_y):
        """Display (or move) the insertion-line indicator at the slot a
        drop at `local_y` (item-local coordinates) would land in."""
        if self._insert_preview_y != local_y:
            self._insert_preview_y = local_y
            self.update()

    def clear_insert_preview(self):
        if self._insert_preview_y is not None:
            self._insert_preview_y = None
            self.update()

    def _subitem_insert_index(self, local_y):
        """Given a local y coordinate, return the index a *new* subitem
        should be inserted at - i.e. before the first existing subitem
        whose row center is below local_y, or at the end if it's past
        everything. Unlike _reorder_target_index() this never excludes
        an index, since it's choosing a slot for a subitem that isn't
        in the list yet."""
        for idx, r in self._subitem_rects:
            if local_y < r.center().y():
                return idx
        return len(self.subitems)

    def _sub_text_title_height(self, item, avail_w):
        """Height (and font) needed for a "text" subitem's bold title
        line, if it's a Text Note with show_title on and non-empty text -
        shared by paint() and _estimate_content_height() so the two never
        disagree about how much vertical space a subitem needs."""
        if item.get("note_type") != "text" or not item.get("show_title") or not item.get("title"):
            return 0, None
        title_font = (
            _font_from_dict(item.get("title_font"), base_family="Segoe UI", base_size=11.0, base_bold=True)
            if item.get("title_font") else QFont("Segoe UI", 11, QFont.Bold)
        )
        # Measure the same rich QTextDocument that actually gets painted
        # (see _get_subitem_rich_doc/paint()'s kind == "text" branch)
        # instead of QFontMetrics.boundingRect() on the plain text - the
        # two don't always agree on wrapped-line height (bold/color runs,
        # rounding), and boundingRect's estimate could come out shorter
        # than the real layout once the title wraps onto two or more
        # lines. That mismatch previously sized the title row too short,
        # clipping the last line off - mirrors the identical fix already
        # applied to _sub_text_body_height for the same reason.
        title_doc = self._get_subitem_rich_doc(
            item, "title", item.get("title_html"), item.get("title", ""), title_font, avail_w)
        h = title_doc.size().height() + 4
        return max(18, h), title_font

    def _sub_text_body_height(self, item, avail_w, sub_font):
        """Height needed for a "text" subitem's body - shared by paint()
        and _estimate_content_height() so the two never disagree about
        how much vertical space the body needs, mirroring
        _sub_media_chrome/_sub_text_title_height's approach for the same
        reason.

        This measures the same QTextDocument that actually gets painted
        (see _get_subitem_rich_doc/_paint_rich_doc) instead of running
        QFontMetrics.boundingRect() on the plain text: the two don't
        always agree on wrapped-line height, and boundingRect's estimate
        could come out shorter than the QTextDocument's real layout for
        a multi-line body. That mismatch was previously sizing the row
        (and the clip rect used to paint it) too short, so the tail of a
        multi-line Text Note subitem got clipped off - and every subitem
        below it in the card then overlapped that too-short row instead
        of starting below its real bottom edge."""
        text = item.get("text", "")
        doc = self._get_subitem_rich_doc(item, "text", item.get("text_html"), text, sub_font, avail_w)
        return doc.size().height() + 4

    def _sub_media_chrome(self, item, avail_w):
        """For an image/gif/video subitem, decide whether its title/desc
        bars should be drawn (on AND actually has text) and how tall each
        one is - shared by paint() and _estimate_content_height() so the
        two never disagree about how much vertical space a subitem needs.
        Each bar grows past its minimum height once its text wraps to
        more than one line, mirroring _paint_sub_media_title/_desc's own
        font/width so the measured height always matches what's actually
        painted."""
        show_title = bool(item.get("show_title", True)) and bool(item.get("title"))
        show_desc = bool(item.get("show_description", True)) and bool(item.get("description"))
        text_w = max(1.0, avail_w - 12)
        title_h = 0
        if show_title:
            title_font = QFont("Segoe UI", 9, QFont.Bold)
            title_doc = self._get_subitem_rich_doc(item, "title", item.get("title_html"),
                                                     item.get("title", ""), title_font, text_w)
            title_h = max(self.SUB_MEDIA_TITLE_H, title_doc.size().height() + 8)
        desc_h = 0
        if show_desc:
            desc_font = QFont("Segoe UI", 8)
            desc_doc = self._get_subitem_rich_doc(item, "description", item.get("description_html"),
                                                    item.get("description", ""), desc_font, text_w)
            desc_h = max(self.SUB_MEDIA_DESC_H, desc_doc.size().height() + 8)
        return show_title, show_desc, title_h, desc_h

    def _paint_sub_media_title(self, painter, rect, item):
        painter.setPen(Qt.NoPen)
        painter.setBrush(QColor(item.get("color")) if item.get("color") else QColor("#1e1e1e"))
        painter.drawRect(rect)
        font = QFont("Segoe UI", 9, QFont.Bold)
        text_rect = rect.adjusted(6, 0, -6, 0)
        doc = self._get_subitem_rich_doc(item, "title", item.get("title_html"), item.get("title", ""),
                                          font, text_rect.width())
        doc_h = doc.size().height()
        paint_rect = QRectF(text_rect.x(), text_rect.y() + (text_rect.height() - doc_h) / 2,
                             text_rect.width(), doc_h)
        _paint_rich_doc(painter, doc, paint_rect, QColor("#ffffff"))

    def _paint_sub_media_desc(self, painter, rect, item):
        painter.setPen(Qt.NoPen)
        painter.setBrush(QColor(item.get("color")) if item.get("color") else QColor("#1e1e1e"))
        painter.drawRect(rect)
        font = QFont("Segoe UI", 8)
        text_rect = rect.adjusted(6, 0, -6, 0)
        doc = self._get_subitem_rich_doc(item, "description", item.get("description_html"),
                                          item.get("description", ""), font, text_rect.width())
        doc_h = doc.size().height()
        paint_rect = QRectF(text_rect.x(), text_rect.y() + (text_rect.height() - doc_h) / 2,
                             text_rect.width(), doc_h)
        _paint_rich_doc(painter, doc, paint_rect, QColor("#aaaaaa"))

    def _estimate_content_height(self):
        """Approximate the total height needed to show every subitem
        without anything getting clipped - mirrors the layout math in
        paint(), but without needing an active QPainter, so it can also
        run right after a subitem is added/edited (see add_subitem(),
        dropEvent(), _sync_subitem_text()) to grow the card to fit instead
        of leaving new content invisible until the user manually resizes
        it. This intentionally only decides whether to grow - the actual
        per-frame layout/clipping in paint() remains the source of truth
        for what's drawn where."""
        y = self._title_h + 6
        pad = 8
        avail_w = max(1, self._w - pad * 2)
        for item in self.subitems:
            kind = item.get("kind")
            if kind in ("image", "gif"):
                pm = base64_to_pixmap(item.get("data", ""))
                _, _, title_h, desc_h = self._sub_media_chrome(item, avail_w)
                h = self._subitem_media_height(pm, avail_w, 10 ** 6) + title_h + desc_h
                y += h + self.MEDIA_GAP
            elif kind == "video":
                aspect = item.get("aspect") or (9 / 16)
                _, _, title_h, desc_h = self._sub_media_chrome(item, avail_w)
                h = (self._subitem_media_height(None, avail_w, 10 ** 6, aspect=aspect)
                     + self.VIDEO_HANDLE_H + title_h + desc_h)
                y += h + self.MEDIA_GAP
            elif kind == "text":
                sub_font = QFont(item.get("font_family") or "Segoe UI", 10)
                sub_font.setBold(bool(item.get("bold")))
                sub_font.setItalic(bool(item.get("italic")))
                sub_font.setUnderline(bool(item.get("underline")))
                needed_h = self._sub_text_body_height(item, avail_w, sub_font)
                title_h, _ = self._sub_text_title_height(item, avail_w)
                strip_h = (self.TOP_STRIP_H + 4) if item.get("top_strip_enabled") else 0
                y += strip_h + max(20, needed_h) + title_h + 8
            elif kind == "checklist":
                y += 22 * len(item.get("items", [])) + 6
        return y + pad

    def _autogrow_to_fit(self):
        needed_h = self._estimate_content_height()
        if needed_h > self._h:
            self.set_size(self._w, needed_h)

    # -- subitem hit-testing / drag-out / reorder ------------------------
    def _subitem_index_at(self, local_pos):
        for idx, r in self._subitem_rects:
            if r.contains(local_pos):
                return idx
        return None

    def _toggle_subitem_checkbox_at(self, idx, local_pos):
        """A click directly on a checklist glyph (\u2610/\u2611) at the
        start of a line inside a "text" subitem toggles it, mirroring
        TextNoteItem._toggle_checkbox_at for a standalone Text Note.

        A "text" subitem's body is only ever drawn as a static rich-text
        document in paint() (see _paint_rich_doc) rather than through a
        live QGraphicsTextItem, so it never went through
        TextNoteItem.mousePressEvent's checkbox handling at all - every
        click anywhere on the subitem (including right on its checkbox)
        was instead claimed unconditionally by mousePressEvent to start
        a drag/reorder, which is why a checklist Text Note that could be
        checked off fine on its own could no longer be checked off once
        dropped into a Board Card. This is checked first, before that
        drag/reorder capture, so a checkbox click is handled here instead."""
        if idx is None or idx >= len(self.subitems):
            return False
        item = self.subitems[idx]
        if item.get("kind") != "text" or not item.get("text"):
            return False
        rect = None
        for i, r in self._subitem_rects:
            if i == idx:
                rect = r
                break
        if rect is None:
            return False
        pad = 8
        avail_w = self._w - pad * 2
        title_h, _ = self._sub_text_title_height(item, avail_w)
        body_top = rect.y() + title_h
        if local_pos.y() < body_top:
            return False
        sub_font = QFont(item.get("font_family") or "Segoe UI", 10)
        sub_font.setBold(bool(item.get("bold")))
        sub_font.setItalic(bool(item.get("italic")))
        sub_font.setUnderline(bool(item.get("underline")))
        body_doc = self._get_subitem_rich_doc(
            item, "text", item.get("text_html"), item.get("text", ""), sub_font, avail_w)
        body_pos = QPointF(local_pos.x() - rect.x(), local_pos.y() - body_top)
        hit = body_doc.documentLayout().hitTest(body_pos, Qt.FuzzyHit)
        if hit < 0:
            return False
        block = body_doc.findBlock(hit)
        block_text = block.text()
        if not block_text[:1] in (CHECK_UNCHECKED, CHECK_CHECKED):
            return False
        # Only react to clicks right on (or just after) the glyph itself,
        # not anywhere else in the line's text.
        if hit - block.position() > 2:
            return False
        new_char = CHECK_CHECKED if block_text[0] == CHECK_UNCHECKED else CHECK_UNCHECKED
        cur = QTextCursor(block)
        cur.movePosition(QTextCursor.Right, QTextCursor.KeepAnchor, 1)
        cur.insertText(new_char)
        item["text"] = body_doc.toPlainText()
        item["text_html"] = body_doc.toHtml()
        # Force _get_subitem_rich_doc to rebuild from the now-updated
        # text/html next time it's asked for this field, instead of
        # handing back the (now stale-keyed) cache entry it made above.
        self._subitem_rich_doc_cache.pop((id(item), "text"), None)
        self.update()
        return True

    @staticmethod
    def _subitem_media_height(pm, avail_w, remaining_h, aspect=None, min_h=40, max_h=None):
        """Compute the reserved box height for an image/gif/video subitem
        so that its box matches the media's real aspect ratio (height/width)
        - this is what lets the media be drawn with KeepAspectRatio and
        exactly fill the box with no cropping and no empty bars, at any
        card width.

        max_h is only applied if the caller explicitly asks for one - a
        blanket default cap here would clamp the box's height while its
        width stayed at avail_w, so a tall/long image would end up
        scaled down to fit that capped height and no longer fill the
        box's full width, appearing pillarboxed instead of "exactly
        fill the box" as promised above. The only height limit that
        should apply unconditionally is however much room is actually
        left in the card (remaining_h)."""
        if aspect is None:
            if pm is not None and not pm.isNull() and pm.width() > 0:
                aspect = pm.height() / pm.width()
            else:
                aspect = 9 / 16
        h = avail_w * aspect
        if max_h is not None:
            h = min(h, max_h)
        return max(min_h, min(h, remaining_h))

    def _get_or_create_video_proxy(self, subitem):
        """Return the embedded VideoPlayerNode for this "video" subitem,
        creating it (and decoding its bytes into a temp file via
        set_video_bytes) the first time it's painted. Reused afterwards -
        position/resize happens every paint() call, but the
        QMediaPlayer/temp file are only ever set up once."""
        key = id(subitem)
        node = self._video_proxies.get(key)
        if node is not None:
            return node
        video_bytes = base64.b64decode(subitem["data"]) if subitem.get("data") else b""
        node = VideoPlayerNode(video_bytes, parent=self)
        node.setZValue(2)
        self._video_proxies[key] = node
        return node

    def _prune_video_proxies(self):
        """Tear down the player node for any "video" subitem that is no
        longer in self.subitems (currently only happens when one is
        dragged out into its own standalone component - see
        mouseReleaseEvent), so playback stops and the node doesn't
        linger invisibly as a child of this card."""
        live_ids = {id(s) for s in self.subitems if s.get("kind") == "video"}
        for key in [k for k in self._video_proxies if k not in live_ids]:
            node = self._video_proxies.pop(key)
            if getattr(node, "player", None) is not None:
                node.player.stop()
            node.setParentItem(None)
            if node.scene() is not None:
                node.scene().removeItem(node)

    def _get_scaled_subitem_pixmap(self, subitem, pm, target_size):
        """Cached pm.scaled(target_size, ...) for an image/gif subitem -
        see _subitem_scaled_cache above. Recomputed only when the target
        box size changes or the source pixmap's content actually changed
        (new gif frame / different image), not on every repaint."""
        key = id(subitem)
        cache_key = pm.cacheKey()
        entry = self._subitem_scaled_cache.get(key)
        if entry is not None and entry[0] == target_size and entry[1] == cache_key:
            return entry[2]
        scaled = pm.scaled(target_size, Qt.KeepAspectRatio, Qt.SmoothTransformation)
        self._subitem_scaled_cache[key] = (target_size, cache_key, scaled)
        return scaled

    def _prune_subitem_scaled_cache(self):
        """Drop cached scaled pixmaps (see _get_scaled_subitem_pixmap) for
        any subitem no longer in self.subitems, mirroring the other
        subitem caches' prune methods above."""
        live_ids = {id(s) for s in self.subitems}
        for key in [k for k in self._subitem_scaled_cache if k not in live_ids]:
            del self._subitem_scaled_cache[key]

    def _get_or_create_image_pixmap(self, subitem):
        """Return the decoded (full-resolution) QPixmap for this "image"
        subitem, decoding it from base64 only the first time it's
        painted instead of on every single repaint - see
        _image_pixmap_cache above for why this matters."""
        key = id(subitem)
        pm = self._image_pixmap_cache.get(key)
        if pm is not None:
            return pm
        pm = base64_to_pixmap(subitem.get("data", ""))
        self._image_pixmap_cache[key] = pm
        return pm

    def _prune_image_pixmap_cache(self):
        """Drop cached pixmaps (see _get_or_create_image_pixmap) for any
        subitem no longer in self.subitems, mirroring
        _prune_video_proxies/_prune_gif_movies above."""
        live_ids = {id(s) for s in self.subitems if s.get("kind") == "image"}
        for key in [k for k in self._image_pixmap_cache if k not in live_ids]:
            del self._image_pixmap_cache[key]

    def _get_or_create_gif_movie(self, subitem):
        """Return the {"movie", "buffer", "pixmap"} entry driving this
        "gif" subitem's animation, creating it the first time it's
        painted. The QMovie's frameChanged signal keeps "pixmap" current
        and schedules a repaint, which is what makes it actually animate
        (a plain base64_to_pixmap() decode, as image subitems use, only
        ever shows one static frame)."""
        key = id(subitem)
        entry = self._gif_movies.get(key)
        if entry is not None:
            return entry
        data = base64.b64decode(subitem["data"]) if subitem.get("data") else b""
        buf = QBuffer(self)
        buf.setData(data)
        buf.open(QIODevice.ReadOnly)
        movie = QMovie(self)
        movie.setDevice(buf)
        entry = {"movie": movie, "buffer": buf, "pixmap": QPixmap()}

        def _on_frame(_frame_no, entry=entry, movie=movie):
            entry["pixmap"] = movie.currentPixmap()
            self.update()

        movie.frameChanged.connect(_on_frame)
        movie.start()
        self._gif_movies[key] = entry
        return entry

    def _prune_gif_movies(self):
        """Stop and drop the QMovie for any "gif" subitem no longer in
        self.subitems, mirroring _prune_video_proxies above."""
        live_ids = {id(s) for s in self.subitems if s.get("kind") == "gif"}
        for key in [k for k in self._gif_movies if k not in live_ids]:
            entry = self._gif_movies.pop(key)
            entry["movie"].stop()

    def _get_subitem_rich_doc(self, item, field, html, plain_text, font, width):
        """Cached QTextDocument for painting one subitem field's stored
        rich text (see _paint_rich_doc) - rebuilt only when the field's
        html/text/font/width actually changed since the last paint()."""
        key = (id(item), field)
        font_key = (font.family(), font.pointSizeF(), font.bold(), font.italic(), font.underline())
        entry = self._subitem_rich_doc_cache.get(key)
        if (entry is not None and entry["html"] == html and entry["text"] == plain_text
                and entry["font_key"] == font_key and abs(entry["width"] - width) < 0.5):
            return entry["doc"]
        doc = QTextDocument()
        doc.setDefaultFont(font)
        doc.setDocumentMargin(0)
        if html:
            doc.setHtml(html)
        else:
            doc.setPlainText(plain_text or "")
        doc.setTextWidth(max(1.0, width))
        self._subitem_rich_doc_cache[key] = {
            "html": html, "text": plain_text, "font_key": font_key, "width": width, "doc": doc,
        }
        return doc

    def _prune_rich_doc_cache(self):
        """Drop cached documents (see _get_subitem_rich_doc) for any
        subitem no longer in self.subitems, mirroring
        _prune_video_proxies/_prune_gif_movies above."""
        live_ids = {id(s) for s in self.subitems}
        for key in [k for k in self._subitem_rich_doc_cache if k[0] not in live_ids]:
            del self._subitem_rich_doc_cache[key]

    def _reorder_target_index(self, y):
        """Given a local y coordinate, figure out which slot the dragged
        subitem should land in if dropped now."""
        for idx, r in self._subitem_rects:
            if idx == self._drag_sub_index:
                continue
            if y < r.center().y():
                return idx
        return max(0, len(self.subitems) - 1)

    def hoverMoveEvent(self, event):
        if self.isSelected() and self.handle_rect().contains(event.pos()):
            self.setCursor(Qt.SizeFDiagCursor)
        elif self._subitem_index_at(event.pos()) is not None:
            self.setCursor(Qt.OpenHandCursor)
        else:
            self.setCursor(Qt.ArrowCursor)
        # Deliberately skip BaseComponentItem.hoverMoveEvent to avoid
        # setting the cursor twice; call QGraphicsObject's directly.
        QGraphicsObject.hoverMoveEvent(self, event)

    def mousePressEvent(self, event):
        self._raised_this_press = False
        if event.button() == Qt.LeftButton and not (
            self.isSelected() and self.handle_rect().contains(event.pos())
        ):
            idx = self._subitem_index_at(event.pos())
            if idx is not None:
                if self._toggle_subitem_checkbox_at(idx, event.pos()):
                    event.accept()
                    return
                self._drag_sub_index = idx
                self._drag_sub_moved = False
                self._drag_sub_start_pos = event.pos()
                self._drag_sub_will_detach = False
                event.accept()
                return
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if self._drag_sub_index is not None:
            local_pos = event.pos()
            if not self._drag_sub_moved:
                moved = (local_pos - self._drag_sub_start_pos).manhattanLength()
                if moved < 6:
                    event.accept()
                    return
                self._drag_sub_moved = True
                self._raise_to_front_if_needed()
                if self.scene() is not None:
                    self._drag_ghost = SubitemDragGhost(self.subitems[self._drag_sub_index])
                    self.scene().addItem(self._drag_ghost)

            inside = self.rect().contains(local_pos)
            self._drag_sub_will_detach = not inside
            if inside:
                new_idx = self._reorder_target_index(local_pos.y())
                if new_idx is not None and new_idx != self._drag_sub_index:
                    sub = self.subitems.pop(self._drag_sub_index)
                    self.subitems.insert(new_idx, sub)
                    self._drag_sub_index = new_idx
            if self._drag_ghost is not None:
                self._drag_ghost.will_detach = self._drag_sub_will_detach
                self._drag_ghost.setPos(event.scenePos() + QPointF(14, 14))
                self._drag_ghost.update()
            self.update()
            event.accept()
            return
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        if self._drag_sub_index is not None:
            idx = self._drag_sub_index
            moved = self._drag_sub_moved
            will_detach = self._drag_sub_will_detach
            self._drag_sub_index = None
            self._drag_sub_will_detach = False
            if self._drag_ghost is not None:
                if self._drag_ghost.scene() is not None:
                    self._drag_ghost.scene().removeItem(self._drag_ghost)
                self._drag_ghost = None
            if moved and will_detach:
                self._detach_subitem(idx, event.scenePos())
            elif not moved:
                # A plain click (no drag) - select this subitem so it
                # gets the same top-toolbar editing (Color, and for a
                # "text" subitem, Font/B/I/U) a standalone component
                # gets when simply clicked/selected outside a card.
                # Double-clicking still opens the in-place text editor
                # exactly as before (see mouseDoubleClickEvent) - this
                # is a separate, non-editing "selected" state.
                self._select_subitem(idx)
            self.update()
            event.accept()
            return
        super().mouseReleaseEvent(event)

    def _select_subitem(self, idx):
        """Mark subitem `idx` as selected (single click, not editing) -
        see _selected_sub_index. Routed through the scene so only one
        subitem across the whole app is ever selected this way at a
        time (mirrors normal component selection), and so the top
        toolbar refreshes to show its Color/Font controls."""
        scene = self.scene()
        if scene is not None and hasattr(scene, "select_board_subitem"):
            scene.select_board_subitem(self, idx)
        else:
            self._selected_sub_index = idx
        self.update()
        mw = getattr(scene, "main_window", None) if scene is not None else None
        if mw is not None:
            mw.on_selection_changed()

    def _detach_subitem(self, idx, scene_pos):
        """Pop subitem `idx` off this card and turn it back into a
        standalone, freely movable canvas component centered on
        `scene_pos` - shared by the drag-it-out-of-the-card gesture
        (mouseReleaseEvent above) and the "Convert Back to Drawing"
        context-menu entry (contextMenuEvent below), which is really
        the same operation just triggered without a drag."""
        sub = self.subitems.pop(idx)
        if self._selected_sub_index is not None:
            # Indices below the removed one are unaffected; anything at
            # or above it shifts down by one (or, if it was the removed
            # subitem itself - not possible here since a subitem can't
            # be both dragged and selected at once, but kept for safety
            # against stale indices - just clear it).
            if self._selected_sub_index > idx:
                self._selected_sub_index -= 1
            elif self._selected_sub_index == idx:
                self._selected_sub_index = None
        self._prune_video_proxies()
        self._prune_gif_movies()
        self._prune_rich_doc_cache()
        self._prune_image_pixmap_cache()
        self._prune_subitem_scaled_cache()
        new_item = subitem_to_component(sub, scene_pos.x() - 100, scene_pos.y() - 60)
        if new_item is not None and self.scene() is not None:
            self.scene().addItem(new_item)
            self.scene().bring_to_front(new_item)
            self.scene().clearSelection()
            new_item.setSelected(True)
        self.update()
        return new_item

    def paint(self, painter, option, widget=None):
        painter.setRenderHint(QPainter.Antialiasing)
        rect = self.rect()
        path = QPainterPath()
        path.addRoundedRect(rect, 10, 10)
        painter.setBrush(QColor(self.color or self.DEFAULT_COLOR))
        pen = QPen(QColor("#4c8bf5") if self.isSelected() else QColor("#111111"),
                   2 if self.isSelected() else 1)
        painter.setPen(pen)
        painter.drawPath(path)

        painter.save()
        painter.setClipPath(path)
        painter.setPen(Qt.NoPen)
        painter.setBrush(QColor("#1e1e1e"))
        painter.drawRect(QRectF(0, 0, self._w, self._title_h))
        painter.restore()
        self._paint_top_strip(painter, clip_path=path)

        y = self._title_h + 6
        pad = 8
        avail_w = self._w - pad * 2
        self._subitem_rects = []
        self._subitem_td_click_rects = {}
        for idx, item in enumerate(self.subitems):
            remaining_h = self._h - y - pad
            if remaining_h < 18:
                break
            kind = item.get("kind")
            row_top = y
            if kind in ("image", "gif"):
                if item.get("top_strip_enabled"):
                    painter.setPen(Qt.NoPen)
                    painter.setBrush(QColor(item.get("top_strip_color") or self.DEFAULT_STRIP_COLOR))
                    painter.drawRect(QRectF(pad, y, avail_w, self.TOP_STRIP_H))
                    y += self.TOP_STRIP_H + 4
                if kind == "gif":
                    # A per-subitem QMovie drives real animation here -
                    # its frameChanged signal keeps this pixmap current
                    # and triggers repaints (see _get_or_create_gif_movie).
                    # A plain base64_to_pixmap() decode, like "image"
                    # subitems use, only ever shows one static first
                    # frame, which is why a gif dropped into a board card
                    # used to sit frozen and only actually animated once
                    # dragged back out into its own standalone component.
                    gif_entry = self._get_or_create_gif_movie(item)
                    pm = gif_entry["pixmap"]
                    if pm.isNull():
                        pm = base64_to_pixmap(item.get("data", ""))
                else:
                    pm = self._get_or_create_image_pixmap(item)
                # Size the reserved box itself to the media's own aspect
                # ratio (instead of a fixed 120px height) so drawing it
                # with KeepAspectRatio below fills the box exactly - no
                # cropping and no letterboxing, and it stays correct no
                # matter how the card gets resized afterwards.
                show_title, show_desc, title_h, desc_h = self._sub_media_chrome(item, avail_w)
                media_h = self._subitem_media_height(pm, avail_w, remaining_h - title_h - desc_h)
                title_click_rect = QRectF(pad, y, avail_w, title_h)
                editing_title = idx == self._sub_edit_index and self._sub_edit_field == "title"
                if show_title and not editing_title:
                    self._paint_sub_media_title(painter, QRectF(pad, y, avail_w, title_h), item)
                if show_title:
                    y += title_h
                r = QRectF(pad, y, avail_w, media_h)
                painter.setBrush(QColor("#111111"))
                painter.setPen(Qt.NoPen)
                painter.drawRect(r)
                if not pm.isNull():
                    scaled = self._get_scaled_subitem_pixmap(item, pm, r.size().toSize())
                    px = r.x() + (r.width() - scaled.width()) / 2
                    py = r.y() + (r.height() - scaled.height()) / 2
                    painter.drawPixmap(int(px), int(py), scaled)
                y += media_h
                desc_click_rect = QRectF(pad, y, avail_w, desc_h)
                editing_desc = idx == self._sub_edit_index and self._sub_edit_field == "description"
                if show_desc and not editing_desc:
                    self._paint_sub_media_desc(painter, QRectF(pad, y, avail_w, desc_h), item)
                if show_desc:
                    y += desc_h
                self._subitem_td_click_rects[idx] = (title_click_rect, desc_click_rect)
                y += self.MEDIA_GAP
                self._subitem_rects.append((idx, QRectF(pad, row_top, avail_w, y - row_top)))
            elif kind == "video":
                if item.get("top_strip_enabled"):
                    painter.setPen(Qt.NoPen)
                    painter.setBrush(QColor(item.get("top_strip_color") or self.DEFAULT_STRIP_COLOR))
                    painter.drawRect(QRectF(pad, y, avail_w, self.TOP_STRIP_H))
                    y += self.TOP_STRIP_H + 4
                # Videos have no decoded thumbnail to measure, but the
                # aspect ratio of the source is stored on the subitem (see
                # component_to_subitem) so the player box keeps the same
                # proportions as image/gif instead of a fixed height. A
                # real VideoWidgetContainer - the same play/seek/mute
                # controls the standalone Video component has - is
                # embedded below a thin drag-strip (so the subitem can
                # still be reordered/dragged out without fighting the
                # player widget for clicks), instead of the old static
                # "\u25B6 video" placeholder that had no playback at all.
                aspect = item.get("aspect") or (9 / 16)
                show_title, show_desc, title_h, desc_h = self._sub_media_chrome(item, avail_w)
                title_click_rect = QRectF(pad, y, avail_w, title_h)
                editing_title = idx == self._sub_edit_index and self._sub_edit_field == "title"
                if show_title and not editing_title:
                    self._paint_sub_media_title(painter, QRectF(pad, y, avail_w, title_h), item)
                if show_title:
                    y += title_h
                media_h = self._subitem_media_height(
                    None, avail_w, remaining_h - self.VIDEO_HANDLE_H - title_h - desc_h, aspect=aspect)
                handle_r = QRectF(pad, y, avail_w, self.VIDEO_HANDLE_H)
                painter.setBrush(QColor("#1e1e1e"))
                painter.setPen(Qt.NoPen)
                painter.drawRect(handle_r)
                painter.setBrush(QColor("#666666"))
                cx = pad + avail_w / 2
                cy = y + self.VIDEO_HANDLE_H / 2
                for i in (-10, 0, 10):
                    painter.drawEllipse(QPointF(cx + i, cy), 1.5, 1.5)
                proxy = self._get_or_create_video_proxy(item)
                proxy.setPos(pad, y + self.VIDEO_HANDLE_H)
                proxy.resize(avail_w, media_h)
                proxy.show()
                y += self.VIDEO_HANDLE_H + media_h
                desc_click_rect = QRectF(pad, y, avail_w, desc_h)
                editing_desc = idx == self._sub_edit_index and self._sub_edit_field == "description"
                if show_desc and not editing_desc:
                    self._paint_sub_media_desc(painter, QRectF(pad, y, avail_w, desc_h), item)
                if show_desc:
                    y += desc_h
                self._subitem_td_click_rects[idx] = (title_click_rect, desc_click_rect)
                y += self.MEDIA_GAP
                self._subitem_rects.append((idx, QRectF(pad, row_top, avail_w, y - row_top)))
            elif kind == "text":
                if item.get("top_strip_enabled"):
                    painter.setPen(Qt.NoPen)
                    painter.setBrush(QColor(item.get("top_strip_color") or self.DEFAULT_STRIP_COLOR))
                    painter.drawRect(QRectF(pad, y, avail_w, self.TOP_STRIP_H))
                    y += self.TOP_STRIP_H + 4
                sub_font = QFont(item.get("font_family") or "Segoe UI", 10)
                sub_font.setBold(bool(item.get("bold")))
                sub_font.setItalic(bool(item.get("italic")))
                sub_font.setUnderline(bool(item.get("underline")))
                self._subitem_font = sub_font
                text = item.get("text", "")
                # A "text" subitem that came from a TextNoteItem (as
                # opposed to a borderless plain-text note, which has no
                # background of its own) carries its background fill in
                # "color" - same field TextNoteItem.paint() uses for its
                # own card background. This was never actually painted
                # here, so changing a Text Note's background color had no
                # visible effect until the note was dragged back out of
                # the Board Card into its own standalone component.
                # A link gets the same blue tint (and underline, so it
                # reads as a link even without hovering) as it would as a
                # standalone Text component; otherwise fall back to the
                # subitem's own stored color if it has one (Text/plaintext
                # components carry their text color in "color"), else the
                # neutral default used before this had any color at all.
                text_color = self._subitem_text_color(item)
                if item.get("link_url"):
                    sub_font.setUnderline(True)
                # Size the row to the text's actual wrapped height (instead
                # of a fixed 50px) so short text doesn't leave a stray gap
                # and long text doesn't spill past its row - previously
                # overflowing text just kept drawing past its row height
                # with nothing clipping it, so it visually bled underneath
                # whatever subitem (e.g. an image) got painted after it.
                title_h, title_font = self._sub_text_title_height(item, avail_w)
                needed_h = self._sub_text_body_height(item, avail_w, sub_font)
                h = min(max(20, needed_h) + title_h, remaining_h)
                r = QRectF(pad, y, avail_w, h)
                editing_title = idx == self._sub_edit_index and self._sub_edit_field == "title"
                editing_text = idx == self._sub_edit_index and self._sub_edit_field == "text"
                painter.save()
                if item.get("note_type") != "plaintext":
                    painter.setPen(Qt.NoPen)
                    painter.setBrush(QColor(item.get("color") or TextNoteItem.DEFAULT_COLOR))
                    bg_path = QPainterPath()
                    bg_path.addRoundedRect(r, 6, 6)
                    painter.drawPath(bg_path)
                painter.setClipRect(r)
                if title_h and not editing_title:
                    title_color = QColor(item.get("title_color")) if item.get("title_color") else text_color
                    title_doc = self._get_subitem_rich_doc(
                        item, "title", item.get("title_html"), item.get("title", ""), title_font, avail_w)
                    _paint_rich_doc(painter, title_doc, QRectF(pad, y, avail_w, title_h), title_color)
                if not editing_text:
                    body_doc = self._get_subitem_rich_doc(
                        item, "text", item.get("text_html"), text, sub_font, avail_w)
                    _paint_rich_doc(painter, body_doc, QRectF(pad, y + title_h, avail_w, h - title_h), text_color)
                painter.restore()
                # Reserved click target for the title bar (only when this
                # subitem actually has a title bar showing - see
                # mouseDoubleClickEvent) so double-clicking it edits the
                # title instead of falling through to the body text.
                self._subitem_td_click_rects[idx] = (
                    QRectF(pad, y, avail_w, title_h) if title_h else None, None
                )
                y += h + 8
                self._subitem_rects.append((idx, QRectF(pad, row_top, avail_w, y - row_top)))
            elif kind == "checklist":
                for line in item.get("items", []):
                    if y > self._h - pad - 16:
                        break
                    box = QRectF(pad, y + 3, 12, 12)
                    painter.setPen(QColor("#aaaaaa"))
                    painter.setBrush(Qt.NoBrush)
                    painter.drawRect(box)
                    painter.setPen(QColor("#dddddd"))
                    painter.drawText(QRectF(pad + 18, y, avail_w - 18, 18), line)
                    y += 22
                y += 6
                self._subitem_rects.append((idx, QRectF(pad, row_top, avail_w, y - row_top)))

            # visual feedback while a subitem is being dragged
            if idx == self._drag_sub_index:
                hl = QRectF(pad, row_top, avail_w, y - row_top - 8)
                painter.setPen(QPen(
                    QColor("#ff6b6b") if self._drag_sub_will_detach else QColor("#4c8bf5"),
                    2, Qt.DashLine,
                ))
                painter.setBrush(Qt.NoBrush)
                painter.drawRect(hl)
            elif idx == self._selected_sub_index:
                # Single-click "selected" state (as opposed to
                # _sub_edit_index, which is actively-being-edited) - a
                # solid border, matching the blue outline a standalone
                # component gets when it's simply selected on the canvas.
                hl = QRectF(pad, row_top, avail_w, y - row_top - 8)
                painter.setPen(QPen(QColor("#4c8bf5"), 2))
                painter.setBrush(Qt.NoBrush)
                painter.drawRect(hl)

        # Insertion-line indicator while a component is being dragged
        # over this card, showing exactly which slot it will land in.
        if self._insert_preview_y is not None:
            idx = self._subitem_insert_index(self._insert_preview_y)
            line_y = None
            for i, r in self._subitem_rects:
                if i == idx:
                    line_y = r.top()
                    break
            if line_y is None:
                # Appending past every existing subitem (including when
                # the card has been resized taller than its content, so
                # there's empty space below the last row): snap the line
                # all the way down to the card's own bottom edge rather
                # than the bottom of the last subitem's rect, so hovering
                # anywhere in that empty space - all the way down to the
                # true bottom edge - reads as "insert at the very end"
                # instead of the line sitting stranded above the cursor.
                line_y = self._h - pad
            painter.setPen(QPen(QColor("#4c8bf5"), 3))
            painter.drawLine(QPointF(pad, line_y), QPointF(self._w - pad, line_y))

        self.paint_handle(painter)

    def dragEnterEvent(self, event):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()

    def dragMoveEvent(self, event):
        event.acceptProposedAction()

    def dropEvent(self, event):
        for url in event.mimeData().urls():
            path = url.toLocalFile()
            ext = os.path.splitext(path)[1].lower()
            try:
                with open(path, "rb") as f:
                    data = f.read()
            except Exception:
                continue
            b64 = base64.b64encode(data).decode("ascii")
            if ext in GIF_EXTS:
                self.add_subitem({"kind": "gif", "data": b64})
            elif ext in VIDEO_EXTS:
                self.add_subitem({"kind": "video", "data": b64})
            elif ext in IMAGE_EXTS:
                self.add_subitem({"kind": "image", "data": b64})
        event.acceptProposedAction()

    def contextMenuEvent(self, event):
        idx = self._subitem_index_at(event.pos())
        if idx is not None:
            sub = self.subitems[idx]
            if sub.get("kind") == "image" and sub.get("drawing_strokes"):
                menu = QMenu()
                convert_action = menu.addAction("Convert Back to Drawing")
                chosen = menu.exec(event.screenPos())
                if chosen == convert_action:
                    self._detach_subitem(idx, event.scenePos())
                return
        super().contextMenuEvent(event)

    def _build_context_menu(self, menu):
        self._build_top_strip_context_menu(menu)
        menu.addSeparator()

    def _handle_context_action(self, action):
        self._handle_top_strip_context_action(action)

    def serialize(self):
        d = super().serialize()
        d["title"] = self.title_item.toPlainText()
        d["subitems"] = self.subitems
        d["title_font"] = _font_to_dict(self.title_item.font())
        d["title_color"] = self.title_item.defaultTextColor().name()
        d["title_html"] = self.title_item.document().toHtml()
        return self._top_strip_serialize(d)

    def to_html(self):
        rows = []
        for item in self.subitems:
            kind = item.get("kind")
            if kind in ("image", "gif", "video"):
                show_title = bool(item.get("show_title", True)) and bool(item.get("title"))
                show_desc = bool(item.get("show_description", True)) and bool(item.get("description"))
                # Prefer the rich per-run HTML captured while editing (see
                # _sync_subitem_field/_end_edit_subitem) so highlight/
                # color/bold/italic/underline runs survive the export -
                # these subitems only exist as plain dict data (no live
                # QGraphicsTextItem), so _rich_html_from_doc_html()
                # rebuilds a throwaway document to walk their formatting.
                title_rich = _rich_html_from_doc_html(
                    item.get("title_html"),
                    base_family=(item.get("title_font") or {}).get("font_family") or "Segoe UI",
                    base_size=(item.get("title_font") or {}).get("font_size") or 10.0,
                ) if show_title else None
                desc_rich = _rich_html_from_doc_html(
                    item.get("description_html"),
                    base_family=(item.get("description_font") or {}).get("font_family") or "Segoe UI",
                    base_size=(item.get("description_font") or {}).get("font_size") or 9.0,
                ) if show_desc else None
                # The subitem's own Background color (set via the Color
                # button/dialog when it's single-click selected - see
                # MainWindow.pick_color) is inlined onto both bars here,
                # same as the standalone component's own export (see
                # MediaCardMixin._title_desc_html) - otherwise it'd only
                # ever show up on the live canvas and the exported HTML
                # would silently fall back to .media-title/.media-desc's
                # #1e1e1e default.
                bg_css = color_to_css(item.get("color")) if item.get("color") else "#1e1e1e"
                t_html = (f'<div class="media-title" style="background:{bg_css}">{title_rich if title_rich else MediaCardMixin._escape_html(item.get("title",""))}</div>'
                          if show_title else "")
                d_html = (f'<div class="media-desc" style="background:{bg_css}">{desc_rich if desc_rich else MediaCardMixin._escape_html(item.get("description",""))}</div>'
                          if show_desc else "")
                if kind == "image":
                    media = f'<img src="data:image/png;base64,{item.get("data","")}"/>'
                    css_class = "sub-image"
                elif kind == "gif":
                    media = f'<img src="data:image/gif;base64,{item.get("data","")}"/>'
                    css_class = "sub-image"
                else:
                    media = f'<video controls src="data:video/mp4;base64,{item.get("data","")}"></video>'
                    css_class = "sub-video"
                strip_html = _subitem_top_strip_html(item)
                pad_style = f"padding-top:{TopStripMixin.TOP_STRIP_H + 4}px;" if strip_html else ""
                rows.append(f'<div class="{css_class}" style="position:relative;{pad_style}">{strip_html}{t_html}{media}{d_html}</div>')
            elif kind == "text":
                title_html = ""
                if item.get("note_type") == "text" and item.get("show_title") and item.get("title"):
                    title_rich = _rich_html_from_doc_html(
                        item.get("title_html"),
                        base_family=(item.get("title_font") or {}).get("font_family") or "Segoe UI",
                        base_size=(item.get("title_font") or {}).get("font_size") or 11.0,
                    )
                    if title_rich:
                        title_text = title_rich
                    else:
                        title_text = (
                            item.get("title", "")
                            .replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
                            .replace("\n", "<br>")
                        )
                    title_html = f'<div style="font-weight:bold;margin-bottom:2px;">{title_text}</div>'
                text_rich = _rich_html_from_doc_html(
                    item.get("text_html"),
                    base_family=item.get("font_family") or "Segoe UI",
                    base_size=item.get("font_size") or 10.0,
                )
                if text_rich:
                    t = text_rich
                else:
                    t = (
                        item.get("text", "")
                        .replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
                        .replace("\n", "<br>")
                    )
                style_bits = [f"font-family:'{item.get('font_family') or 'Segoe UI'}',sans-serif"]
                if item.get("bold"):
                    style_bits.append("font-weight:bold")
                if item.get("italic"):
                    style_bits.append("font-style:italic")
                link_url = item.get("link_url")
                if link_url:
                    style_bits.append("color:#5b9dd9")
                    style_bits.append("text-decoration:underline")
                    safe_url = link_url.replace('"', "&quot;")
                    style = ";".join(style_bits)
                    t = f'<a href="{safe_url}" target="_blank" rel="noopener noreferrer" style="{style}">{t}</a>'
                else:
                    if item.get("underline"):
                        style_bits.append("text-decoration:underline")
                    if item.get("note_type") == "plaintext" and item.get("color"):
                        style_bits.append(f"color:{color_to_css(item.get('color'))}")
                    elif item.get("note_type") == "text" and item.get("text_color"):
                        style_bits.append(f"color:{color_to_css(item.get('text_color'))}")
                    elif not item.get("note_type") and item.get("color"):
                        style_bits.append(f"color:{color_to_css(item.get('color'))}")
                    style = ";".join(style_bits)
                    t = f'<span style="{style}">{t}</span>'
                strip_html = _subitem_top_strip_html(item)
                pad_style = f"padding-top:{TopStripMixin.TOP_STRIP_H + 4}px;" if strip_html else ""
                rows.append(f'<div class="sub-text" style="position:relative;{pad_style}">{strip_html}{title_html}{t}</div>')
            elif kind == "checklist":
                lis = "".join(f'<li><input type="checkbox" disabled> {x}</li>' for x in item.get("items", []))
                rows.append(f'<ul class="sub-checklist">{lis}</ul>')
        # The card's own title is a live QGraphicsTextItem (unlike the
        # subitems above), so its rich per-run formatting can be read
        # straight off its document - no stored-HTML reconstruction
        # needed here.
        tf = self.title_item.font()
        title = _qtextdocument_to_web_html(
            self.title_item.document(), base_family=tf.family(), base_size=tf.pointSizeF())
        bg_css = color_to_css(self.color or self.DEFAULT_COLOR)
        # Same fix as TextNoteItem.to_html: the title's default color
        # (settable via title_color, see __init__) only lives on
        # defaultTextColor(), so un-colored runs need it set explicitly
        # here instead of silently inheriting .board-title's CSS default.
        title_color_css = color_to_css(self.title_item.defaultTextColor().name())
        return (
            f'<div class="comp board-card" data-id="{self.id}" style="left:{self.pos().x()}px;top:{self.pos().y()}px;'
            f'width:{self._w}px;min-height:{self._h}px;background:{bg_css};">{self._top_strip_html()}'
            f'<div class="board-title" style="color:{title_color_css};">{title}</div>'
            f'<div class="board-body">{"".join(rows)}</div></div>'
        )


# --------------------------------------------------------------------------
# Board link (shortcut to another board .html file, for nested boards)
# --------------------------------------------------------------------------

class BoardLinkCreateDialog(QDialog):
    """Dialog shown by MainWindow.add_board_link() when creating a new
    board-shortcut card: asks for the board's name and, optionally, lets
    the user pick a thumbnail/icon image (or an .svg file) for it right
    away - the same thumbnail can also be set or changed later from the
    card's own right-click menu, see BoardLinkItem._pick_thumbnail()."""

    def __init__(self, parent=None, initial_name=""):
        super().__init__(parent)
        self.setWindowTitle("New board link")
        self.thumb_mime = None
        self.thumb_data = None

        layout = QVBoxLayout(self)

        form = QFormLayout()
        self.name_edit = QLineEdit(initial_name)
        self.name_edit.setPlaceholderText("Board name")
        form.addRow("Board name:", self.name_edit)
        layout.addLayout(form)

        thumb_row = QHBoxLayout()
        self.thumb_preview = QLabel("No\nthumbnail")
        self.thumb_preview.setFixedSize(64, 64)
        self.thumb_preview.setAlignment(Qt.AlignCenter)
        self.thumb_preview.setStyleSheet(
            "background:#1b1b1b; border:1px solid #444; border-radius:6px; color:#777; font-size:10px;"
        )
        thumb_row.addWidget(self.thumb_preview)

        btn_col = QVBoxLayout()
        choose_btn = QPushButton("Choose Image/SVG\u2026")
        choose_btn.clicked.connect(self._choose_thumbnail)
        btn_col.addWidget(choose_btn)
        self.clear_btn = QPushButton("Remove Thumbnail")
        self.clear_btn.clicked.connect(self._clear_thumbnail)
        self.clear_btn.setEnabled(False)
        btn_col.addWidget(self.clear_btn)
        thumb_row.addLayout(btn_col)
        thumb_row.addStretch(1)
        layout.addLayout(thumb_row)

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self._on_accept)
        buttons.rejected.connect(self.reject)
        layout.addWidget(buttons)

        self.name_edit.setFocus()

    def _choose_thumbnail(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "Choose thumbnail image",
            "", "Images and SVG (*.png *.jpg *.jpeg *.bmp *.webp *.gif *.svg)",
        )
        if not path:
            return
        mime, data = load_thumb_file(path)
        if not mime:
            QMessageBox.warning(
                self, "Unsupported file",
                "Please choose an image (PNG/JPG/BMP/WEBP/GIF) or an SVG file.",
            )
            return
        self.thumb_mime, self.thumb_data = mime, data
        pm = thumb_to_pixmap(mime, data, size=64)
        if pm is not None and not pm.isNull():
            self.thumb_preview.setPixmap(pm)
        else:
            self.thumb_preview.setText("Preview\nunavailable")
        self.clear_btn.setEnabled(True)

    def _clear_thumbnail(self):
        self.thumb_mime = None
        self.thumb_data = None
        self.thumb_preview.setPixmap(QPixmap())
        self.thumb_preview.setText("No\nthumbnail")
        self.clear_btn.setEnabled(False)

    def _on_accept(self):
        if not self.name_edit.text().strip():
            QMessageBox.warning(self, "Name required", "Please enter a board name.")
            return
        self.accept()

    def board_name(self):
        return self.name_edit.text().strip()


class BoardLinkItem(BaseComponentItem):
    """A card that is a *shortcut* to another board .html file living in
    the same project folder (as opposed to BoardCardItem, which nests
    content directly inside the current board). Double-clicking it - or
    picking "Open Board" from its right-click menu - navigates the whole
    app window to that file, the same way clicking a board card in
    Milanote drills into it. The referenced file is tracked purely by
    its (relative) filename, since every board of a project lives flat
    in the project's folder - see MainWindow.add_board_link().
    """
    TYPE_NAME = "board_link"
    DEFAULT_COLOR = "#233047"
    # Same default text color as TextNoteItem, so the description field
    # reads exactly like a Text Note's body text against this card's own
    # dark background.
    DEFAULT_DESC_COLOR = "#e8e8e8"
    DESC_MIN_H = 30

    def __init__(self, x=0, y=0, w=220, h=120, title="Board", target_file="", item_id=None,
                 thumb_mime=None, thumb_data=None, description="", show_description=False,
                 description_font=None, description_color=None, description_html=None):
        super().__init__(x, y, w, h, item_id)
        self.title = title or "Board"
        self.target_file = target_file or ""
        # Optional toggleable description field - toggled via the same
        # "Show Description" toolbar checkbox / context-menu entry idea
        # as Text Note's "Title" toggle, and backed by the exact same
        # EditableTextItem field TextNoteItem uses for its own body text
        # (see TextNoteItem.text_item above), just parented to this card
        # instead and painted below the title/subtitle.
        self.show_description = bool(show_description)
        self._desc_h = 0
        self._desc_autosizing = False
        self.description_item = EditableTextItem(self)
        self.description_item.setDefaultTextColor(
            QColor(description_color) if description_color else QColor(self.DEFAULT_DESC_COLOR)
        )
        self.description_item.setFont(
            _font_from_dict(description_font, base_family="Segoe UI", base_size=11.0)
            if description_font else QFont("Segoe UI", 11)
        )
        self.description_item.setPlainText(description)
        self.description_item.setTextInteractionFlags(Qt.NoTextInteraction)
        self.description_item.document().setDocumentMargin(0)
        if description_html:
            self.description_item.document().setHtml(description_html)
        self.description_item.setVisible(self.show_description)
        self.description_item.document().contentsChanged.connect(self._on_description_changed)
        # Optional custom icon/thumbnail for this shortcut card - an
        # uploaded image or SVG file, stored (and exported) as a base64
        # `data:` URI exactly like any other embedded image. Set/changed
        # via the "Set Thumbnail..." context-menu entry, or up front in
        # the "New board link" dialog - see _pick_thumbnail() and
        # MainWindow.add_board_link().
        self.thumb_mime = thumb_mime or None
        self.thumb_data = thumb_data or None
        self._thumb_pixmap = None
        self._thumb_pixmap_dirty = True
        self.min_w, self.min_h = 140, 90
        # Filled in lazily by _refresh_count() the first time this item is
        # painted (and again after a rename/creation), so the card can show
        # a Milanote-style "N cards" subtitle without re-reading the target
        # file on every single repaint.
        self._cached_count = None
        self._count_stale = True

    # -- helpers ----------------------------------------------------------
    def _main_window(self):
        scene = self.scene()
        if scene is None:
            return None
        views = scene.views()
        return views[0].window() if views else None

    def _project_dir(self):
        mw = self._main_window()
        if mw is not None and getattr(mw, "current_file", None):
            return os.path.dirname(mw.current_file)
        return None

    def _target_path(self):
        proj = self._project_dir()
        if not proj or not self.target_file:
            return None
        return os.path.join(proj, self.target_file)

    def mark_count_stale(self):
        self._count_stale = True
        self.update()

    # -- description (toggleable text field, same mechanics as
    #    TextNoteItem's own body text) -------------------------------
    def _recalc_desc_height(self):
        """Fit the description band to its current text - grows for a
        longer description, same idea as TextNoteItem._recalc_title_height,
        never shrinks below DESC_MIN_H."""
        self.description_item.setTextWidth(max(10, self._w - 24))
        if not self.show_description:
            self._desc_h = 0
            return
        doc_h = self.description_item.document().size().height()
        self._desc_h = max(self.DESC_MIN_H, doc_h + 14)

    def _desc_bar_h(self):
        return self._desc_h if self.show_description else 0

    def font_targets(self, editing_item=None):
        """What the toolbar's Font/B/I/U/Size controls (and the Color
        button while editing - see MainWindow.pick_color) should restyle:
        the description field, exactly like TextNoteItem.font_targets
        returns its own single text_item."""
        return [self.description_item]

    def _grow_by_desc_delta(self, old_desc_h):
        """Common tail of toggling/typing the description: fit the card's
        own height to however much the description band just grew or
        shrank, the same auto-sizing idea as TextNoteItem._on_text_changed
        (grows for more text, shrinks back down for less, guarded against
        re-entrant recalculation while resizing)."""
        delta = self._desc_h - old_desc_h
        if not delta:
            return
        self._desc_autosizing = True
        try:
            self.set_size(self._w, self._h + delta)
        finally:
            self._desc_autosizing = False

    def _toggle_show_description(self):
        self.show_description = not self.show_description
        self.description_item.setVisible(self.show_description)
        old_desc_h = self._desc_h
        self._recalc_desc_height()
        self._grow_by_desc_delta(old_desc_h)
        self.update()

    def _on_description_changed(self):
        if self._desc_autosizing:
            return
        old_desc_h = self._desc_h
        self._recalc_desc_height()
        if self.show_description:
            self._grow_by_desc_delta(old_desc_h)
        self.update()

    def on_resized(self):
        self._recalc_desc_height()

    # -- thumbnail/icon ---------------------------------------------------
    def set_thumbnail(self, mime, data):
        """Set (mime, data) to a base64 `data:` payload to give this card
        a custom icon/thumbnail, or (None, None) to remove it and fall
        back to the plain shortcut glyph."""
        self.thumb_mime = mime or None
        self.thumb_data = data or None
        self._thumb_pixmap_dirty = True
        self.update()

    def _get_thumb_pixmap(self):
        if self._thumb_pixmap_dirty:
            self._thumb_pixmap_dirty = False
            self._thumb_pixmap = (
                thumb_to_pixmap(self.thumb_mime, self.thumb_data, size=160)
                if self.thumb_data else None
            )
        return self._thumb_pixmap

    def _refresh_count(self):
        if not self._count_stale:
            return
        self._count_stale = False
        path = self._target_path()
        if not path or not os.path.exists(path):
            self._cached_count = None
            return
        try:
            with open(path, "r", encoding="utf-8") as f:
                html = f.read()
        except Exception:
            self._cached_count = None
            return
        # Fast path: just the small mindmap-meta tag - present on any
        # board saved since this existed, and cheap regardless of how
        # many/how large the images on the target board are, since it
        # never touches the (potentially many-megabyte) main data blob.
        meta = extract_scene_meta(html)
        if meta is not None and "item_count" in meta:
            self._cached_count = meta["item_count"]
            return
        # Fallback for a board saved by an older version of the app,
        # before mindmap-meta existed: this decodes the *entire* target
        # board, images included, purely to count its items - genuinely
        # slow for a photo-heavy board, which is why paint() only ever
        # calls this once per rename/creation (see _count_stale) rather
        # than on every repaint. Re-saving the target file adds the meta
        # tag, so this slow path is only ever hit once per such file.
        try:
            data = extract_scene_data(html)
            self._cached_count = len(data.get("items", [])) if data else 0
        except Exception:
            self._cached_count = None

    # -- painting -----------------------------------------------------
    def paint(self, painter, option, widget=None):
        self._refresh_count()
        self._recalc_desc_height()
        rect = self.rect()
        painter.setRenderHint(QPainter.Antialiasing)
        bg = QColor(self.color or self.DEFAULT_COLOR)
        painter.setBrush(bg)
        painter.setPen(QPen(QColor("#4c8bf5"), 2) if self.isSelected() else QPen(QColor("#111111"), 1))
        painter.drawRoundedRect(rect, 10, 10)

        # Leave room at the bottom for the (optional) description band,
        # exactly like TextNoteItem reserves _title_bar_h() at the top -
        # everything else below (thumbnail/title/subtitle) lays out
        # inside content_h instead of the card's full height.
        desc_h = self._desc_bar_h()
        content_h = max(40.0, rect.height() - desc_h)

        missing = self.target_file and self._project_dir() and not os.path.exists(self._target_path() or "")
        thumb = self._get_thumb_pixmap()

        if thumb is not None and not thumb.isNull():
            # Custom thumbnail: bleed it across the top of the card (clipped
            # to the card's own rounded outline) and push the title/subtitle
            # into the band below it.
            img_h = max(40.0, content_h * 0.58)
            img_rect = QRectF(0, 0, rect.width(), img_h)
            painter.save()
            clip_path = QPainterPath()
            clip_path.addRoundedRect(rect, 10, 10)
            painter.setClipPath(clip_path)
            painter.setClipRect(img_rect, Qt.IntersectClip)
            scaled = thumb.scaled(img_rect.size().toSize(), Qt.KeepAspectRatioByExpanding, Qt.SmoothTransformation)
            sx = img_rect.center().x() - scaled.width() / 2.0
            sy = img_rect.center().y() - scaled.height() / 2.0
            painter.drawPixmap(QPointF(sx, sy), scaled)
            painter.restore()

            # small "shortcut" glyph badge, overlaid on the thumbnail
            badge_rect = QRectF(rect.width() - 30, img_h - 22, 20, 20)
            painter.setPen(Qt.NoPen)
            painter.setBrush(QColor("#5b9dd9") if not missing else QColor("#c0554a"))
            painter.drawRoundedRect(badge_rect, 4, 4)
            painter.setPen(QPen(QColor("#ffffff"), 2))
            painter.drawLine(badge_rect.bottomLeft() + QPointF(3, -3), badge_rect.topRight() + QPointF(-3, 3))
            painter.drawLine(badge_rect.topRight() + QPointF(-3, 3), badge_rect.topRight() + QPointF(-9, 3))
            painter.drawLine(badge_rect.topRight() + QPointF(-3, 3), badge_rect.topRight() + QPointF(-3, 9))

            painter.setPen(QColor("#ffffff"))
            painter.setFont(QFont("Segoe UI", 11, QFont.Bold))
            title_rect = QRectF(12, img_h + 6, rect.width() - 24, content_h - img_h - 28)
            painter.drawText(title_rect, Qt.TextWordWrap | Qt.AlignLeft | Qt.AlignTop, self.title)

            sub_rect = QRectF(12, content_h - 20, rect.width() - 24, 16)
        else:
            # small "shortcut" glyph in the top-left corner (plain layout,
            # used whenever no custom thumbnail has been set)
            icon_rect = QRectF(12, 12, 20, 20)
            painter.setPen(Qt.NoPen)
            painter.setBrush(QColor("#5b9dd9") if not missing else QColor("#c0554a"))
            painter.drawRoundedRect(icon_rect, 4, 4)
            painter.setPen(QPen(QColor("#ffffff"), 2))
            painter.drawLine(icon_rect.bottomLeft() + QPointF(3, -3), icon_rect.topRight() + QPointF(-3, 3))
            painter.drawLine(icon_rect.topRight() + QPointF(-3, 3), icon_rect.topRight() + QPointF(-9, 3))
            painter.drawLine(icon_rect.topRight() + QPointF(-3, 3), icon_rect.topRight() + QPointF(-3, 9))

            painter.setPen(QColor("#ffffff"))
            painter.setFont(QFont("Segoe UI", 11, QFont.Bold))
            title_rect = QRectF(12, 38, rect.width() - 24, content_h - 60)
            painter.drawText(title_rect, Qt.TextWordWrap | Qt.AlignLeft | Qt.AlignTop, self.title)

            sub_rect = QRectF(12, content_h - 24, rect.width() - 24, 18)

        painter.setFont(QFont("Segoe UI", 8))
        if missing:
            painter.setPen(QColor("#e08a80"))
            painter.drawText(sub_rect, Qt.AlignLeft | Qt.AlignVCenter, "Board file missing")
        else:
            painter.setPen(QColor("#9aa4b2"))
            count = self._cached_count
            label = f"{count} card{'s' if count != 1 else ''}" if count is not None else "Open board \u2192"
            painter.drawText(sub_rect, Qt.AlignLeft | Qt.AlignVCenter, label)

        if self.show_description:
            painter.setPen(QPen(QColor(255, 255, 255, 40), 1))
            painter.drawLine(QPointF(12, content_h), QPointF(rect.width() - 12, content_h))
            self.description_item.setPos(12, content_h + 6)
            self.description_item.setTextWidth(max(10, rect.width() - 24))

        self.paint_handle(painter)

    # -- navigation -----------------------------------------------------
    def mouseDoubleClickEvent(self, event):
        if self.show_description and event.pos().y() >= (self._h - self._desc_bar_h()):
            self.description_item.setTextInteractionFlags(Qt.TextEditorInteraction)
            self.description_item.setFocus()
            cursor = self.description_item.textCursor()
            cursor.select(QTextCursor.Document)
            self.description_item.setTextCursor(cursor)
            event.accept()
            return
        self.open_board()
        event.accept()

    def open_board(self):
        mw = self._main_window()
        path = self._target_path()
        if mw is None:
            return
        if not self.target_file:
            return
        if not path or not os.path.exists(path):
            QMessageBox.warning(
                mw, "Board missing",
                f"The board file \u201c{self.target_file}\u201d could not be found in the project folder."
            )
            return
        mw.navigate_to_file(path)

    # -- context menu -----------------------------------------------------
    def _build_context_menu(self, menu):
        self._open_action = menu.addAction("Open Board")
        menu.addSeparator()
        self._desc_menu_action = menu.addAction("Description")
        self._desc_menu_action.setCheckable(True)
        self._desc_menu_action.setChecked(self.show_description)
        menu.addSeparator()
        self._rename_action = menu.addAction("Rename Board (File && References)\u2026")
        self._set_thumb_action = menu.addAction(
            "Change Thumbnail\u2026" if self.thumb_data else "Set Thumbnail\u2026"
        )
        self._clear_thumb_action = menu.addAction("Remove Thumbnail") if self.thumb_data else None
        menu.addSeparator()
        self._remove_ref_action = menu.addAction("Remove Reference (keep board file)")
        self._remove_ref_and_file_action = menu.addAction("Remove Reference && Delete Board File\u2026")
        menu.addSeparator()

    def _handle_context_action(self, action):
        if action == self._open_action:
            self.open_board()
        elif action == self._desc_menu_action:
            self._toggle_show_description()
        elif action == self._rename_action:
            self._rename_referenced_board()
        elif action == self._set_thumb_action:
            self._pick_thumbnail()
        elif self._clear_thumb_action is not None and action == self._clear_thumb_action:
            self.set_thumbnail(None, None)
            mw = self._main_window()
            if mw is not None and mw.current_file:
                mw._write_html(mw.current_file)
        elif action == self._remove_ref_action:
            self._remove_reference(delete_file=False)
        elif action == self._remove_ref_and_file_action:
            self._remove_reference(delete_file=True)

    # -- thumbnail picking --------------------------------------------------
    def _pick_thumbnail(self):
        mw = self._main_window()
        path, _ = QFileDialog.getOpenFileName(
            mw, "Choose thumbnail image",
            "", "Images and SVG (*.png *.jpg *.jpeg *.bmp *.webp *.gif *.svg)",
        )
        if not path:
            return
        mime, data = load_thumb_file(path)
        if not mime:
            QMessageBox.warning(
                mw, "Unsupported file",
                "Please choose an image (PNG/JPG/BMP/WEBP/GIF) or an SVG file.",
            )
            return
        self.set_thumbnail(mime, data)
        if mw is not None and mw.current_file:
            mw._write_html(mw.current_file)

    # -- rename / refactor --------------------------------------------------
    def _rename_referenced_board(self):
        """Rename the board this shortcut points at: renames the actual
        .html file on disk *and* rewrites every other reference to it -
        board_link cards and breadcrumb entries - found across every
        sibling .html file in the project folder, so nothing is left
        pointing at the old filename."""
        mw = self._main_window()
        if mw is None:
            return
        proj = self._project_dir()
        if not proj or not self.target_file:
            QMessageBox.information(
                mw, "Cannot rename", "This reference has no linked board file yet."
            )
            return
        old_path = self._target_path()
        if not old_path or not os.path.exists(old_path):
            QMessageBox.warning(
                mw, "Cannot rename", "The linked board file could not be found on disk."
            )
            return

        old_target_file = self.target_file
        old_name_no_ext = os.path.splitext(old_target_file)[0]
        new_name, ok = QInputDialog.getText(
            mw, "Rename board", "New board name:", text=old_name_no_ext
        )
        if not ok or not new_name.strip():
            return
        safe_new_name = sanitize_board_filename(new_name)
        new_target_file = safe_new_name + ".html"
        if new_target_file == old_target_file:
            return
        new_path = os.path.join(proj, new_target_file)
        if os.path.exists(new_path):
            QMessageBox.warning(
                mw, "Rename failed",
                f"A file named \u201c{new_target_file}\u201d already exists in the project folder.",
            )
            return

        # 1. Rename the actual board file on disk.
        try:
            os.rename(old_path, new_path)
        except Exception as e:
            QMessageBox.critical(mw, "Rename failed", str(e))
            return

        # 2. Fix up the renamed file's own breadcrumb (its last segment is
        #    itself), then walk every *other* sibling .html file in the
        #    project folder and update any board_link item or breadcrumb
        #    segment that still points at the old filename/name.
        try:
            with open(new_path, "r", encoding="utf-8") as f:
                data = extract_scene_data(f.read()) or {"items": []}
            breadcrumb = data.get("breadcrumb") or []
            if breadcrumb:
                breadcrumb[-1] = {"name": safe_new_name, "file": new_target_file}
            data["breadcrumb"] = breadcrumb
            with open(new_path, "w", encoding="utf-8") as f:
                f.write(build_html_document(data))
        except Exception:
            pass

        updated = _apply_rename_to_project_siblings(
            proj, old_target_file, old_name_no_ext, new_target_file, safe_new_name,
            skip_path=new_path,
        )

        # 3. Update this card, and - if this board is the one currently on
        #    screen - every other in-memory BoardLinkItem/breadcrumb entry
        #    pointing at the old name, so the rename shows up immediately
        #    without needing a reload, then persist that board too.
        self.target_file = new_target_file
        self.title = safe_new_name
        self._count_stale = True
        self.update()

        if mw.scene is self.scene():
            for it in mw.scene.items():
                if isinstance(it, BoardLinkItem) and it is not self and it.target_file == old_target_file:
                    it.target_file = new_target_file
                    if it.title == old_name_no_ext:
                        it.title = safe_new_name
                    it.mark_count_stale()
            for i, seg in enumerate(mw.breadcrumb):
                if seg.get("file") == old_target_file:
                    mw.breadcrumb[i] = {"name": safe_new_name, "file": new_target_file}
            mw._update_breadcrumb_bar()
            if mw.current_file:
                mw._write_html(mw.current_file)

        mw.statusBar().showMessage(
            f"Renamed board to \u201c{new_target_file}\u201d ({updated} other file(s) updated)", 5000
        )

    def _remove_reference(self, delete_file):
        mw = self._main_window()
        if delete_file:
            path = self._target_path()
            msg = (
                f"Delete the board \u201c{self.title}\u201d ({self.target_file}) from disk?\n\n"
                "This removes this shortcut AND permanently deletes the board file "
                "itself. Any other shortcuts elsewhere that point to the same file "
                "will stop working."
            )
            if QMessageBox.question(
                mw, "Delete board file", msg,
                QMessageBox.Yes | QMessageBox.No, QMessageBox.No,
            ) != QMessageBox.Yes:
                return
            if path and os.path.exists(path):
                try:
                    os.remove(path)
                except Exception as e:
                    QMessageBox.critical(mw, "Delete failed", str(e))
                    return
        if self.scene():
            self.scene().removeItem(self)

    # -- serialization --------------------------------------------------
    def serialize(self):
        d = super().serialize()
        d["title"] = self.title
        d["target_file"] = self.target_file
        if self.thumb_data:
            d["thumb_mime"] = self.thumb_mime
            d["thumb_data"] = self.thumb_data
        d["description"] = self.description_item.toPlainText()
        d["show_description"] = self.show_description
        d["description_font"] = _font_to_dict(self.description_item.font())
        d["description_color"] = self.description_item.defaultTextColor().name()
        # Full rich-text fidelity, same pattern as TextNoteItem.serialize's
        # text_html - the plain "description" string above stays as a
        # simple fallback for anything that only reads that.
        d["description_html"] = self.description_item.document().toHtml()
        return d

    def to_html(self):
        title = self.title.replace("&", "&amp;").replace("<", "&lt;")
        href = (self.target_file or "#").replace('"', "&quot;")
        thumb_html = ""
        if self.thumb_data:
            # Embedded exactly like any other image in the app - a plain
            # base64 `data:` URI, self-contained inside the exported HTML.
            thumb_html = f'<img class="board-link-thumb" src="data:{self.thumb_mime};base64,{self.thumb_data}"/>'
        desc_html = ""
        if self.show_description and self.description_item.toPlainText().strip():
            # Same helper TextNoteItem.to_html uses, so the exported
            # description mirrors exactly what's shown in the app,
            # per-character formatting included.
            df = self.description_item.font()
            desc_text = _qtextdocument_to_web_html(
                self.description_item.document(), base_family=df.family(), base_size=df.pointSizeF()
            )
            desc_color_css = color_to_css(self.description_item.defaultTextColor().name())
            desc_html = f'<div class="board-link-desc" style="color:{desc_color_css}">{desc_text}</div>'
        return (
            f'<a class="comp board-link-card" data-id="{self.id}" href="{href}" '
            f'style="left:{self.pos().x()}px;top:{self.pos().y()}px;'
            f'width:{self._w}px;height:{self._h}px;">'
            f'{thumb_html}'
            f'<div class="board-link-title">{title}</div>'
            f'<div class="board-link-sub">Open board \u2192</div>'
            f'{desc_html}</a>'
        )


# --------------------------------------------------------------------------
# Component <-> subitem conversion, and deserialization factory
# --------------------------------------------------------------------------

def component_to_subitem(item):
    if isinstance(item, ImageItem):
        return {
            "kind": "image", "data": pixmap_to_base64(item.pixmap_orig),
            # Title/description are kept, along with whether each is
            # currently shown, so they come back exactly as they were -
            # both while embedded in a card (see BoardCardItem.paint())
            # and if the subitem is later dragged back out into its own
            # standalone component (see subitem_to_component).
            "title": item.title_item.toPlainText(),
            "description": item.description_item.toPlainText(),
            "show_title": item.show_title,
            "show_description": item.show_description,
            "title_font": _font_to_dict(item.title_item.font()),
            "description_font": _font_to_dict(item.description_item.font()),
            "title_color": item.title_item.defaultTextColor().name(),
            "description_color": item.description_item.defaultTextColor().name(),
            # Rich per-character formatting (bold/italic/underline/color/
            # highlight runs) - see BoardCardItem.to_html(), which needs
            # this to export the same highlight that shows in the app.
            "title_html": item.title_item.document().toHtml(),
            "description_html": item.description_item.document().toHtml(),
            "color": item.color,
            "top_strip_enabled": item.top_strip_enabled,
            "top_strip_color": item.top_strip_color,
            # The standalone item's own size/opacity - purely so
            # subitem_to_component can restore them if it's later
            # dragged back out; the card itself always lays this
            # subitem out at its own column width regardless of these.
            "w": item._w,
            "h": item._h,
            "opacity": item.opacity(),
        }
    if isinstance(item, GifItem):
        return {
            "kind": "gif",
            "data": base64.b64encode(item.gif_bytes).decode("ascii") if item.gif_bytes else "",
            "title": item.title_item.toPlainText(),
            "description": item.description_item.toPlainText(),
            "show_title": item.show_title,
            "show_description": item.show_description,
            "title_font": _font_to_dict(item.title_item.font()),
            "description_font": _font_to_dict(item.description_item.font()),
            "title_color": item.title_item.defaultTextColor().name(),
            "description_color": item.description_item.defaultTextColor().name(),
            "title_html": item.title_item.document().toHtml(),
            "description_html": item.description_item.document().toHtml(),
            "color": item.color,
            "top_strip_enabled": item.top_strip_enabled,
            "top_strip_color": item.top_strip_color,
            "w": item._w,
            "h": item._h,
            "opacity": item.opacity(),
        }
    if isinstance(item, VideoItem):
        return {
            "kind": "video",
            "data": base64.b64encode(item.video_bytes).decode("ascii") if item.video_bytes else "",
            # Store the standalone item's own aspect ratio so the Board
            # Card can reserve a same-proportions box for it too, even
            # though (unlike image/gif) there is no decoded frame to
            # measure from directly.
            "aspect": (item._h / item._w) if item._w else (9 / 16),
            "title": item.title_item.toPlainText(),
            "description": item.description_item.toPlainText(),
            "show_title": item.show_title,
            "show_description": item.show_description,
            "title_font": _font_to_dict(item.title_item.font()),
            "description_font": _font_to_dict(item.description_item.font()),
            "title_color": item.title_item.defaultTextColor().name(),
            "description_color": item.description_item.defaultTextColor().name(),
            "title_html": item.title_item.document().toHtml(),
            "description_html": item.description_item.document().toHtml(),
            "color": item.color,
            "top_strip_enabled": item.top_strip_enabled,
            "top_strip_color": item.top_strip_color,
            "w": item._w,
            "h": item._h,
            "opacity": item.opacity(),
        }
    if isinstance(item, (TextNoteItem, PlainTextItem)):
        f = item.text_item.font()
        d = {
            "kind": "text",
            "text": item.text_item.toPlainText(),
            # Which standalone component this came from, so dragging it
            # back out (see subitem_to_component) restores the same kind
            # instead of always turning into a Text Note - and its link
            # and styling, which used to be silently dropped here.
            "note_type": "plaintext" if isinstance(item, PlainTextItem) else "text",
            "link_url": item.link_url,
            "color": item.color,
            "text_color": getattr(item, "text_color", None),
            "font_family": f.family(),
            "font_size": f.pointSizeF(),
            "bold": f.bold(),
            "italic": f.italic(),
            "underline": f.underline(),
            # Rich per-character formatting (bold/italic/underline/color/
            # highlight runs) - see BoardCardItem.to_html(), which needs
            # this to export the same highlight that shows in the app.
            "text_html": item.text_item.document().toHtml(),
            # Own size/opacity, restored on drag-out only (see "w"/"h"/
            # "opacity" comment on the ImageItem branch above).
            "w": item._w,
            "h": item._h,
            "opacity": item.opacity(),
        }
        if isinstance(item, TextNoteItem):
            # A Text Note's own title (and whether it's shown) used to be
            # dropped here entirely - dragging the note into a card, then
            # back out, silently reset it to a hidden default "Title".
            d["title"] = item.title_item.toPlainText()
            d["show_title"] = item.show_title
            d["title_font"] = _font_to_dict(item.title_item.font())
            d["title_html"] = item.title_item.document().toHtml()
            d["top_strip_enabled"] = item.top_strip_enabled
            d["top_strip_color"] = item.top_strip_color
        return d
    if isinstance(item, DrawingItem):
        img = QImage(max(1, int(item._w)), max(1, int(item._h)), QImage.Format_ARGB32)
        img.fill(Qt.transparent)
        p = QPainter(img)
        p.setRenderHint(QPainter.Antialiasing)
        for s in item.strokes:
            pts = s.get("points", [])
            if len(pts) < 2:
                continue
            pen = QPen(QColor(s.get("color", "#ffffff")))
            pen.setWidth(max(1, int(s.get("width", 3))))
            pen.setCapStyle(Qt.RoundCap)
            pen.setJoinStyle(Qt.RoundJoin)
            p.setPen(pen)
            path = QPainterPath()
            path.moveTo(pts[0][0], pts[0][1])
            for pt in pts[1:]:
                path.lineTo(pt[0], pt[1])
            p.drawPath(path)
        p.end()
        pm = QPixmap.fromImage(img)
        # Dropping a Draw sketch onto a Board Card only has a rasterized
        # "image" subitem kind to land in - there's no vector "drawing"
        # subitem kind. Stash the original stroke data (and the canvas
        # size it was drawn at) alongside the flattened pixmap so the
        # card's "Convert Back to Drawing" context menu entry can
        # reconstruct a real, still-editable DrawingItem later instead
        # of only ever being able to pull the flat picture back out.
        return {
            "kind": "image",
            "data": pixmap_to_base64(pm),
            "drawing_strokes": copy.deepcopy(item.strokes),
            "drawing_w": item._w,
            "drawing_h": item._h,
            "opacity": item.opacity(),
        }
    return None


def subitem_to_component(subitem, x, y):
    """Reverse of component_to_subitem: turn a board-card subitem back into
    a standalone, freely movable canvas component (used when a subitem is
    dragged out of its board card)."""
    kind = subitem.get("kind")
    if kind == "image" and subitem.get("drawing_strokes"):
        # This "image" subitem started life as a Draw sketch that got
        # rasterized when it was dropped onto the card (see
        # component_to_subitem) - the original vector strokes were kept
        # around specifically so it can come back as a real, still-
        # editable DrawingItem instead of a flat picture.
        w = subitem.get("drawing_w") or 100
        h = subitem.get("drawing_h") or 100
        it = DrawingItem(x, y, w, h, strokes=copy.deepcopy(subitem.get("drawing_strokes", [])))
        if subitem.get("opacity") is not None:
            it.setOpacity(subitem.get("opacity"))
        return it
    if kind == "image":
        it = ImageItem(x, y, w=subitem.get("w") or 240, h=subitem.get("h") or 180,
                        b64=subitem.get("data"),
                        title=subitem.get("title", ""), description=subitem.get("description", ""),
                        show_title=subitem.get("show_title", True),
                        show_description=subitem.get("show_description", True),
                        title_font=subitem.get("title_font"), desc_font=subitem.get("description_font"),
                        title_color=subitem.get("title_color"), desc_color=subitem.get("description_color"),
                        # Rich per-character title/description formatting
                        # (bold/italic/underline/color/highlight runs) -
                        # without these, dragging the subitem back out
                        # silently flattened it to plain text (see
                        # component_to_subitem, which does capture these,
                        # and deserialize_component, which already passes
                        # them through on a normal file load).
                        title_html=subitem.get("title_html"), desc_html=subitem.get("description_html"),
                        top_strip_enabled=subitem.get("top_strip_enabled", False),
                        top_strip_color=subitem.get("top_strip_color"))
        if subitem.get("color"):
            it.set_color(subitem.get("color"))
        if subitem.get("opacity") is not None:
            it.setOpacity(subitem.get("opacity"))
        return it
    if kind == "gif":
        it = GifItem(x, y, w=subitem.get("w") or 240, h=subitem.get("h") or 180,
                      b64=subitem.get("data"),
                      title=subitem.get("title", ""), description=subitem.get("description", ""),
                      show_title=subitem.get("show_title", True),
                      show_description=subitem.get("show_description", True),
                      title_font=subitem.get("title_font"), desc_font=subitem.get("description_font"),
                      title_color=subitem.get("title_color"), desc_color=subitem.get("description_color"),
                      title_html=subitem.get("title_html"), desc_html=subitem.get("description_html"),
                      top_strip_enabled=subitem.get("top_strip_enabled", False),
                      top_strip_color=subitem.get("top_strip_color"))
        if subitem.get("color"):
            it.set_color(subitem.get("color"))
        if subitem.get("opacity") is not None:
            it.setOpacity(subitem.get("opacity"))
        return it
    if kind == "video":
        it = VideoItem(x, y, w=subitem.get("w") or 320, h=subitem.get("h") or 220,
                        b64=subitem.get("data"),
                        title=subitem.get("title", ""), description=subitem.get("description", ""),
                        show_title=subitem.get("show_title", True),
                        show_description=subitem.get("show_description", True),
                        title_font=subitem.get("title_font"), desc_font=subitem.get("description_font"),
                        title_color=subitem.get("title_color"), desc_color=subitem.get("description_color"),
                        title_html=subitem.get("title_html"), desc_html=subitem.get("description_html"),
                        top_strip_enabled=subitem.get("top_strip_enabled", False),
                        top_strip_color=subitem.get("top_strip_color"))
        if subitem.get("color"):
            it.set_color(subitem.get("color"))
        if subitem.get("opacity") is not None:
            it.setOpacity(subitem.get("opacity"))
        return it
    if kind == "text":
        cls = PlainTextItem if subitem.get("note_type") == "plaintext" else TextNoteItem
        default_w, default_h = (220, 50) if cls is PlainTextItem else (220, 140)
        kwargs = dict(
            w=subitem.get("w") or default_w, h=subitem.get("h") or default_h,
            text=subitem.get("text", ""),
            color=subitem.get("color"),
            font_family=subitem.get("font_family"),
            font_size=subitem.get("font_size"),
            bold=subitem.get("bold", False),
            italic=subitem.get("italic", False),
            underline=subitem.get("underline", False),
            link_url=subitem.get("link_url"),
            text_html=subitem.get("text_html"),
        )
        if cls is TextNoteItem:
            kwargs["text_color"] = subitem.get("text_color")
            kwargs["title"] = subitem.get("title", "Title")
            kwargs["show_title"] = subitem.get("show_title", False)
            kwargs["title_font"] = subitem.get("title_font")
            kwargs["title_html"] = subitem.get("title_html")
            kwargs["top_strip_enabled"] = subitem.get("top_strip_enabled", False)
            kwargs["top_strip_color"] = subitem.get("top_strip_color")
        it = cls(x, y, **kwargs)
        if subitem.get("opacity") is not None:
            it.setOpacity(subitem.get("opacity"))
        return it
    if kind == "checklist":
        # No standalone checklist component exists yet, so fall back to a
        # plain text note listing the checklist items.
        text = "\n".join(f"\u2022 {t}" for t in subitem.get("items", []))
        return TextNoteItem(x, y, text=text or "Checklist")
    return None


ANCHOR_TARGET_TYPES = (TextNoteItem, ImageItem, GifItem, VideoItem, BoardCardItem)


def deserialize_component(d):
    t = d.get("type")
    x, y, w, h = d.get("x", 0), d.get("y", 0), d.get("w", 200), d.get("h", 150)
    item_id = d.get("id")
    if t == "text":
        item = TextNoteItem(
            x, y, w, h, text=d.get("text", ""), color=d.get("color"), item_id=item_id,
            font_family=d.get("font_family"), font_size=d.get("font_size"),
            bold=d.get("bold", False), italic=d.get("italic", False),
            underline=d.get("underline", False), link_url=d.get("link_url"),
            text_color=d.get("text_color"),
            title=d.get("title", "Title"), show_title=d.get("show_title", False),
            title_font=d.get("title_font"),
            text_html=d.get("text_html"), title_html=d.get("title_html"),
        )
    elif t == "plaintext":
        item = PlainTextItem(
            x, y, w, h, text=d.get("text", ""), color=d.get("color"), item_id=item_id,
            font_family=d.get("font_family"), font_size=d.get("font_size"),
            bold=d.get("bold", False), italic=d.get("italic", False),
            underline=d.get("underline", False), link_url=d.get("link_url"),
            text_html=d.get("text_html"),
        )
    elif t == "image":
        item = ImageItem(x, y, w, h, b64=d.get("data"), item_id=item_id,
                          title=d.get("title", ""), description=d.get("description", ""),
                          show_title=d.get("show_title", True),
                          show_description=d.get("show_description", True),
                          title_font=d.get("title_font"), desc_font=d.get("description_font"),
                          title_color=d.get("title_color"), desc_color=d.get("description_color"),
                          title_html=d.get("title_html"), desc_html=d.get("description_html"))
    elif t == "gif":
        item = GifItem(x, y, w, h, b64=d.get("data"), item_id=item_id,
                        title=d.get("title", ""), description=d.get("description", ""),
                        show_title=d.get("show_title", True),
                        show_description=d.get("show_description", True),
                        title_font=d.get("title_font"), desc_font=d.get("description_font"),
                        title_color=d.get("title_color"), desc_color=d.get("description_color"),
                        title_html=d.get("title_html"), desc_html=d.get("description_html"))
    elif t == "video":
        item = VideoItem(x, y, w, h, b64=d.get("data"), item_id=item_id,
                          title=d.get("title", ""), description=d.get("description", ""),
                          show_title=d.get("show_title", True),
                          show_description=d.get("show_description", True),
                          title_font=d.get("title_font"), desc_font=d.get("description_font"),
                          title_color=d.get("title_color"), desc_color=d.get("description_color"),
                          title_html=d.get("title_html"), desc_html=d.get("description_html"))
    elif t == "drawing":
        item = DrawingItem(x, y, w, h, strokes=d.get("strokes", []), item_id=item_id,
                            allow_board_card=d.get("allow_board_card", False))
    elif t == "arrow":
        p1 = d.get("p1")
        p2 = d.get("p2")
        item = ArrowItem(
            x, y, w, h,
            p1=tuple(p1) if p1 else None,
            p2=tuple(p2) if p2 else None,
            color=d.get("color"),
            stroke_width=d.get("stroke_width", 4),
            style=d.get("style", "single"),
            line_style=d.get("line_style", "solid"),
            item_id=item_id,
            label=d.get("label", ""),
            show_label=d.get("show_label", False),
            label_font=d.get("label_font"),
            label_color=d.get("label_color"),
            label_html=d.get("label_html"),
            anchor1=d.get("anchor1"),
            anchor2=d.get("anchor2"),
        )
    elif t == "board":
        item = BoardCardItem(x, y, w, h, title=d.get("title", "Board"), subitems=d.get("subitems", []),
                              item_id=item_id, title_font=d.get("title_font"), title_color=d.get("title_color"),
                              title_html=d.get("title_html"))
    elif t == "board_link":
        item = BoardLinkItem(
            x, y, w, h, title=d.get("title", "Board"), target_file=d.get("target_file", ""),
            item_id=item_id, thumb_mime=d.get("thumb_mime"), thumb_data=d.get("thumb_data"),
            description=d.get("description", ""), show_description=d.get("show_description", False),
            description_font=d.get("description_font"), description_color=d.get("description_color"),
            description_html=d.get("description_html"),
        )
    elif t == "table":
        item = TableItem(
            x, y, w, h, rows=d.get("rows", 3), cols=d.get("cols", 3), item_id=item_id,
            data=d.get("data"), headers=d.get("headers"),
            header_bg=d.get("header_bg"), header_text_color=d.get("header_text_color"),
            text_color=d.get("text_color"), even_row_bg=d.get("even_row_bg"),
            odd_row_bg=d.get("odd_row_bg"), even_row_text_color=d.get("even_row_text_color"),
            odd_row_text_color=d.get("odd_row_text_color"),
            header_fonts=d.get("header_fonts"), data_fonts=d.get("data_fonts"),
            header_htmls=d.get("header_htmls"), data_htmls=d.get("data_htmls"),
            grid_line_color=d.get("grid_line_color"),
            grid_line_width=d.get("grid_line_width"),
        )
    else:
        return None
    item.setZValue(d.get("z", 0))
    if "opacity" in d:
        try:
            item.setOpacity(max(0.0, min(1.0, float(d.get("opacity", 1.0)))))
        except (TypeError, ValueError):
            pass
    if t not in ("text", "plaintext") and d.get("color"):
        # TextNoteItem/PlainTextItem already receive their color via the
        # constructor above; every other type picks it up generically here
        # so "Change Color" round-trips through save/load for all
        # component kinds.
        item.color = d.get("color")
    if isinstance(item, TopStripMixin):
        item.top_strip_enabled = bool(d.get("top_strip_enabled", False))
        if d.get("top_strip_color"):
            item.top_strip_color = d.get("top_strip_color")
    snap_method = d.get("arrow_snap_method")
    item.arrow_snap_method = snap_method if snap_method in ARROW_SNAP_METHODS else None
    return item


# --------------------------------------------------------------------------
# Scene
# --------------------------------------------------------------------------

class _ArrowAnchorEndpointMarkers(QGraphicsObject):
    """Standalone overlay that paints the green anchor-point rings for
    every currently anchored endpoint of the selected arrow(s), in scene
    coordinates, above every normal component (see ARROW_ANCHOR_MARKER_Z).

    ArrowItem itself always paints below every normal component (see
    ARROW_Z_OFFSET), including its own endpoint circles - so an anchored
    endpoint drawn there ends up partly or fully covered by whatever
    component it's stuck to. This item is kept in sync (via
    MindMapScene.update_anchor_endpoint_markers) instead of being part
    of any single arrow, so it can sit in its own always-on-top layer
    independent of the arrow's own z-order.
    """
    R = ArrowItem.ENDPOINT_R

    def __init__(self):
        super().__init__()
        self._points = []
        self.setZValue(ARROW_ANCHOR_MARKER_Z)
        self.setAcceptedMouseButtons(Qt.NoButton)

    def set_points(self, points):
        self.prepareGeometryChange()
        self._points = list(points)
        self.update()

    def boundingRect(self):
        if not self._points:
            return QRectF()
        pad = self.R + 6
        xs = [p.x() for p in self._points]
        ys = [p.y() for p in self._points]
        return QRectF(min(xs) - pad, min(ys) - pad,
                       max(xs) - min(xs) + 2 * pad, max(ys) - min(ys) + 2 * pad)

    def paint(self, painter, option, widget=None):
        painter.setRenderHint(QPainter.Antialiasing)
        for pt in self._points:
            painter.setPen(QPen(QColor("#ffffff"), 2))
            painter.setBrush(QColor("#34c759"))
            painter.drawEllipse(pt, self.R, self.R)
            painter.setPen(QPen(QColor("#34c759"), 1.5))
            painter.setBrush(Qt.NoBrush)
            painter.drawEllipse(pt, self.R + 3, self.R + 3)


# --------------------------------------------------------------------------
# Diagnostics (opt-in): board-switch item/memory snapshots, used to track
# down the "panning/zoom gets heavier the more boards I open" report. Off
# by default so normal usage never pays for it or spams stderr - set
# OPENNOTE_DEBUG_PERF=1 in the environment to turn it on for a debugging
# session. Called from MindMapScene.clear_board()/load() below.
# --------------------------------------------------------------------------
_PERF_DEBUG = os.environ.get("OPENNOTE_DEBUG_PERF") == "1"


def _debug_perf_snapshot(label):
    if not _PERF_DEBUG:
        return
    # gc.collect() first: without it, objects only involved in reference
    # cycles (e.g. Qt signal/slot closures) may still be *pending*
    # collection rather than actually unreachable, which would make a
    # real leak look identical to a merely-not-yet-swept cycle in the
    # counts below.
    gc.collect()
    counts = {}
    for obj in gc.get_objects():
        if isinstance(obj, BaseComponentItem):
            name = type(obj).__name__
            counts[name] = counts.get(name, 0) + 1
    total = sum(counts.values())
    rss_str = "n/a"
    try:
        import resource
        rss_kb = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        # ru_maxrss is KB on Linux, bytes on macOS.
        rss_mb = rss_kb / 1024 if sys.platform != "darwin" else rss_kb / (1024 * 1024)
        rss_str = f"{rss_mb:.1f} MB"
    except Exception:
        pass
    detail = ", ".join(f"{k}={v}" for k, v in sorted(counts.items()))
    print(f"[PERF] {label}: live_component_items={total} ({detail}) | RSS={rss_str}",
          file=sys.stderr)


def _debug_describe_referrers(obj):
    """For a leaked item still reachable after clear_board()'s teardown +
    gc.collect(), walk gc.get_referrers() to name whatever's actually
    holding onto it - a MainWindow/scene attribute (most likely: one of
    the toolbar "current selection" caches like _other_selection /
    _top_strip_selection, if it wasn't re-cleared by a selectionChanged
    handler firing mid-teardown), a stray list, etc. One extra hop is
    walked for list/tuple/set referrers so a "held in a list" result also
    names the *owner* of that list, not just "some list somewhere"."""
    if not _PERF_DEBUG:
        return
    findings = []
    for ref in gc.get_referrers(obj):
        if isinstance(ref, _types.FrameType):
            continue  # this function's own locals, not a real leak
        if isinstance(ref, dict):
            owner = None
            for o in gc.get_referrers(ref):
                if isinstance(o, _types.FrameType):
                    continue
                if getattr(o, "__dict__", None) is ref:
                    owner = o
                    break
            keys = [k for k, v in list(ref.items()) if v is obj]
            findings.append(f"{type(owner).__name__ if owner else '?'}.__dict__ attr(s)={keys}")
        elif isinstance(ref, (list, tuple, set)):
            owner = None
            owner_attr = None
            for o in gc.get_referrers(ref):
                if isinstance(o, _types.FrameType):
                    continue
                if isinstance(o, dict):
                    for oo in gc.get_referrers(o):
                        if isinstance(oo, _types.FrameType):
                            continue
                        if getattr(oo, "__dict__", None) is o:
                            owner = oo
                            owner_attr = [k for k, v in o.items() if v is ref]
                            break
            findings.append(
                f"{type(ref).__name__}(len={len(ref)}) in "
                f"{type(owner).__name__ if owner else '?'}.{owner_attr}"
            )
        else:
            findings.append(type(ref).__name__)
    print(f"[PERF-LEAK] {type(obj).__name__} id={id(obj)} still referenced by: {findings}",
          file=sys.stderr)


class MindMapScene(QGraphicsScene):
    def __init__(self, parent=None):
        super().__init__(parent)
        # Explicit reference to MainWindow (rather than relying on Qt's
        # QObject parent() - parent here is only ever main_window in
        # practice, but storing it directly keeps drawBackground's prefs
        # lookup independent of that assumption). Set right after
        # construction in MainWindow.__init__; may be None briefly during
        # construction/tests, so drawBackground guards for that.
        self.main_window = None
        # Which Board Card subitem (if any) is currently single-click
        # "selected" (as opposed to being actively edited via double-
        # click) - see BoardCardItem._selected_sub_index/_select_subitem.
        # Only one, across every card on the board, at a time - tracked
        # here (rather than just on the card) so a click landing
        # anywhere else can find and clear whichever card currently
        # holds it without needing to know which card that is.
        self._subitem_selected_card = None
        self.setSceneRect(-5000, -5000, 10000, 10000)
        self.setBackgroundBrush(QColor("#101012"))
        self.draw_mode = False
        self.brush_color = QColor("#ffffff")
        self.brush_width = 4
        self.brush_type = "pen"  # pen, marker, highlighter
        self.brush_opacity = 1.0  # 0..1, set via the opacity slider
        self.erase_mode = False  # toggled by the Draw toolbar's Eraser checkbox
        self._erasing = False
        self._current_stroke_points = []
        self._current_preview_item = None
        self._anchor_highlight_item = None
        self._anchors_refreshing = False
        self._anchor_endpoint_markers = None
        # True for the whole duration of a rubber-band drag-select (see
        # MindMapView.mousePressEvent/mouseReleaseEvent). Qt re-evaluates
        # the rubber band's intersection with the scene and emits
        # selectionChanged on essentially every mouseMoveEvent while
        # dragging - on a board with many items that meant
        # update_anchor_endpoint_markers, MainWindow.on_selection_changed
        # (which does dozens of toolbar-widget updates) and
        # MainWindow._flush_pending_undo_checkpoint (which can
        # JSON-serialize the whole board) were all firing dozens of times
        # a second, making the drag itself feel laggy. Those three
        # handlers now bail out immediately while this is True, and the
        # view runs them once, for real, right after the drag ends.
        self.rubber_band_dragging = False
        self.selectionChanged.connect(self.update_anchor_endpoint_markers)

    @staticmethod
    def _is_anchored_arrow(it):
        """True once an arrow has at least one endpoint snapped to a
        component - see bring_to_front()'s docstring for why that's the
        signal used to decide which z-order band it belongs in."""
        return isinstance(it, ArrowItem) and (it.anchor1 is not None or it.anchor2 is not None)

    def select_board_subitem(self, card, idx):
        """Mark subitem `idx` of `card` as single-click "selected" - see
        BoardCardItem._selected_sub_index. Deselects whatever subitem
        (on this card or any other) was selected this way before, so
        only one is ever selected across the whole board at a time,
        mirroring normal component selection."""
        self.clear_board_subitem_selection()
        card._selected_sub_index = idx
        card.update()
        self._subitem_selected_card = card

    def clear_board_subitem_selection(self):
        """Deselect whichever subitem is currently single-click
        "selected" (if any) - called whenever a click lands anywhere
        that isn't that same subitem (see MindMapView.mousePressEvent),
        and whenever that subitem stops existing (deleted, detached,
        or its card removed)."""
        card = self._subitem_selected_card
        if card is not None:
            try:
                card._selected_sub_index = None
                card.update()
            except RuntimeError:
                pass  # underlying Qt object already deleted
            self._subitem_selected_card = None
            # Unlike a subitem being (re-)selected (see select_board_subitem/
            # BoardCardItem._select_subitem), a plain click-away deselect
            # like this one never goes through Qt's own selectionChanged
            # (subitem "selection" was never real Qt selection to begin
            # with - see BoardCardItem.mousePressEvent), so nothing else
            # would ever tell the top toolbar to stop showing this
            # subitem's now-stale Color/Top Strip/Font controls without
            # this explicit refresh.
            mw = getattr(self, "main_window", None)
            if mw is not None:
                mw.on_selection_changed()

    def bring_to_front(self, item):
        """Raise `item` above every other component in its own "band" so
        clicking/dragging it always brings it visually to the front
        *within its own band*, instead of leaving it stuck at whatever
        z-order it happened to be created in.

        A freshly created, not-yet-snapped arrow behaves like any other
        new component: it shares the normal band and lands on top, same
        as a new Text Note/Image/etc. Only once at least one of its
        endpoints is actually anchored to a component (see
        ArrowItem._set_anchor, called from mouseReleaseEvent when an
        endpoint is dropped onto a target) does it drop into its own
        band, offset well below every normal component (see
        ARROW_Z_OFFSET), so an anchored arrow always stacks under every
        other component type - even one that was JUST brought to front -
        matching Arrow's "tucks behind the components it connects"
        behavior. mouseReleaseEvent re-calls bring_to_front() right
        after (un)anchoring so this takes effect the moment an endpoint
        is snapped onto (or pulled off of) a target, not just at
        creation time.
        Freehand Draw strokes are the mirror image: their band sits
        above every normal component (see DRAWING_Z_OFFSET), so a
        sketch always stays visible on top even after some other
        component gets added or brought to front later on.
        Computed fresh from the scene's actual current z-values (rather
        than a stored counter) so it stays correct across load/delete/
        undo."""
        others = [it for it in self.items() if isinstance(it, BaseComponentItem) and it is not item]
        if self._is_anchored_arrow(item):
            band = [it.zValue() for it in others if self._is_anchored_arrow(it)]
            floor = ARROW_Z_OFFSET
        elif isinstance(item, DrawingItem):
            band = [it.zValue() for it in others if isinstance(it, DrawingItem)]
            floor = DRAWING_Z_OFFSET
        else:
            band = [
                it.zValue() for it in others
                if not self._is_anchored_arrow(it) and not isinstance(it, DrawingItem)
            ]
            floor = 0
        item.setZValue(max(band, default=floor - 1) + 1)

    # -- arrow endpoint anchoring (Board Card / Text Note / media) ------
    def _ensure_anchor_highlight(self):
        hl = self._anchor_highlight_item
        if hl is None:
            hl = QGraphicsRectItem()
            hl.setPen(QPen(QColor("#ffffff"), 2))
            hl.setBrush(Qt.NoBrush)
            hl.setZValue(ANCHOR_HIGHLIGHT_Z)
            hl.setVisible(False)
            self.addItem(hl)
            self._anchor_highlight_item = hl
        return hl

    def show_anchor_highlight(self, target_item):
        """Draw (or hide, if target_item is None) a white outline over a
        component while an arrow endpoint is being dragged over it - the
        visual cue that releasing here will anchor the endpoint to it."""
        hl = self._ensure_anchor_highlight()
        if target_item is None:
            hl.setVisible(False)
            return
        rect = target_item.mapToScene(target_item.rect()).boundingRect()
        hl.setRect(rect)
        hl.setVisible(True)

    def hide_anchor_highlight(self):
        self.show_anchor_highlight(None)

    def _ensure_anchor_endpoint_markers(self):
        markers = self._anchor_endpoint_markers
        if markers is None:
            markers = _ArrowAnchorEndpointMarkers()
            self.addItem(markers)
            self._anchor_endpoint_markers = markers
        return markers

    def update_anchor_endpoint_markers(self):
        """Re-collect the anchored-endpoint scene points of every
        currently selected arrow and hand them to the always-on-top
        overlay (see _ArrowAnchorEndpointMarkers) so its green rings
        stay visible above whatever component they're stuck to, no
        matter that the arrow's own paint() runs underneath it.

        Called whenever selection changes (connected in __init__),
        whenever an anchored arrow's geometry is resynced
        (ArrowItem._sync_geometry) - which covers both a live endpoint
        drag and a component it's anchored to moving/resizing - and
        after an item is removed from the scene.
        """
        if self.rubber_band_dragging:
            # Skipped mid-drag for performance (see rubber_band_dragging);
            # MindMapView re-calls this once for real right after the
            # drag ends.
            return
        points = []
        for it in self.items():
            if isinstance(it, ArrowItem) and it.isSelected():
                if it.anchor1 is not None:
                    points.append(it.mapToScene(it.p1))
                if it.anchor2 is not None:
                    points.append(it.mapToScene(it.p2))
        markers = self._ensure_anchor_endpoint_markers()
        markers.set_points(points)
        markers.setVisible(bool(points))

    def refresh_anchored_arrows(self, mover=None):
        """Re-sync every arrow that has an anchored endpoint - called by
        BaseComponentItem whenever a component moves or resizes, so
        anchored arrows keep following it live. Guarded against
        reentrancy since an arrow repositioning itself also triggers
        this same notification. `mover` is whichever item's own move/
        resize triggered this call - passed straight through to each
        arrow's refresh_anchors so it can tell a real target component
        moving (re-orbit) apart from the arrow itself moving (leave its
        anchored endpoint(s) alone) - see ArrowItem.refresh_anchors."""
        if self._anchors_refreshing:
            return
        self._anchors_refreshing = True
        try:
            for it in self.items():
                if isinstance(it, ArrowItem):
                    it.refresh_anchors(mover=mover)
        finally:
            self._anchors_refreshing = False
        self.update_anchor_endpoint_markers()

    def removeItem(self, item):
        for it in self.items():
            if isinstance(it, ArrowItem) and it is not item:
                if it.anchor1 is not None and it.anchor1.get("item") is item:
                    it.anchor1 = None
                if it.anchor2 is not None and it.anchor2.get("item") is item:
                    it.anchor2 = None
        super().removeItem(item)
        if item is self._anchor_endpoint_markers:
            self._anchor_endpoint_markers = None
        else:
            self.update_anchor_endpoint_markers()

    # -- background dot grid ------------------------------------------
    # Dots are drawn in *scene* coordinates with a non-cosmetic pen, so
    # they are transformed together with everything else: zooming in
    # (Ctrl+Wheel) makes the dots visibly bigger and further apart on
    # screen, exactly like the reference screenshots.
    GRID_SPACING = 40
    DOT_SIZE = 2.4
    MIN_SCREEN_SPACING = 18  # once GRID_SPACING would put dots closer than
                              # this many *screen* pixels apart, double the
                              # spacing (see drawBackground) - keeps the
                              # dot count, and so the redraw cost, roughly
                              # constant no matter how far zoomed out

    def drawBackground(self, painter, rect):
        super().drawBackground(painter, rect)
        painter.setRenderHint(QPainter.Antialiasing, False)

        # `rect` is the exposed area in *scene* coordinates, which grows
        # as ~1/scale when zooming out - so at a fixed GRID_SPACING the
        # raw dot count grows quadratically the further out you zoom.
        # At a moderate 20x zoom-out that's on the order of a quarter
        # million dots to place on every single repaint (and several
        # million at 100x) - each one previously its own separate
        # drawPoint() call, which has real per-call overhead on top of
        # that. That combination is exactly what made zooming far out
        # visibly freeze the view. Doubling the spacing every time the
        # on-screen gap between dots would otherwise fall under
        # MIN_SCREEN_SPACING keeps the number of dots - and therefore
        # the redraw cost - roughly flat at any zoom level, the same way
        # Figma/Miro-style canvases keep their background grid affordable
        # however far out you zoom.
        scale = painter.transform().m11() or 1.0

        # Even with the doubling trick above, the capped point set (still
        # a couple thousand QPointF objects, built fresh in Python) is
        # rebuilt and drawn on EVERY repaint - i.e. continuously while
        # panning or zooming, not just once. Skipping it altogether once
        # the view is zoomed out past the user's configured threshold
        # (Preferences > "Optimize grid rendering") removes that constant
        # per-frame cost, and the dots are barely perceptible at that
        # zoom level anyway.
        prefs = getattr(self.main_window, "prefs", None) if self.main_window else None
        if prefs and prefs.get("optimize_grid_rendering", True):
            threshold_pct = prefs.get("grid_disable_zoom_percent", 15.0)
            if scale * 100.0 <= threshold_pct:
                return

        grid = self.GRID_SPACING
        while grid * scale < self.MIN_SCREEN_SPACING:
            grid *= 2

        pen = QPen(QColor(255, 255, 255, 40))
        pen.setWidthF(self.DOT_SIZE)
        pen.setCapStyle(Qt.SquareCap)
        painter.setPen(pen)

        left = int(rect.left()) - (int(rect.left()) % grid)
        top = int(rect.top()) - (int(rect.top()) % grid)
        # Collecting every dot into one list and drawing it with a
        # single drawPoints() call is dramatically faster than the
        # equivalent number of individual drawPoint() calls (each of
        # which pays its own call overhead) - see the note above.
        points = []
        x = left
        while x < rect.right():
            y = top
            while y < rect.bottom():
                points.append(QPointF(x, y))
                y += grid
            x += grid
        if points:
            painter.drawPoints(points)

    # -- drawing mode ---------------------------------------------------
    def _effective_width(self):
        if self.brush_type == "highlighter":
            return max(self.brush_width, 14)
        if self.brush_type == "marker":
            return max(self.brush_width, 8)
        return self.brush_width

    def _stroke_color(self):
        color = QColor(self.brush_color)
        base_alpha = 90 if self.brush_type == "highlighter" else 255
        color.setAlpha(max(0, min(255, int(base_alpha * self.brush_opacity))))
        return color

    def _make_pen(self):
        pen = QPen(self._stroke_color(), self._effective_width())
        pen.setCapStyle(Qt.RoundCap)
        pen.setJoinStyle(Qt.RoundJoin)
        return pen

    # -- eraser (Draw mode's Eraser checkbox) ----------------------------
    ERASER_RADIUS = 16

    def _erase_at(self, scene_pt):
        """Remove whatever part of any DrawingItem's strokes fall within
        ERASER_RADIUS of `scene_pt` - splitting a stroke into separate
        pieces around the erased gap rather than deleting the whole
        stroke, so only the part the cursor actually passed over
        disappears."""
        radius = self.ERASER_RADIUS
        margin = radius + 60
        search_rect = QRectF(scene_pt.x() - margin, scene_pt.y() - margin, margin * 2, margin * 2)
        for it in list(self.items(search_rect)):
            if not isinstance(it, DrawingItem):
                continue
            local_pt = scene_pt - it.pos()
            new_strokes = []
            changed = False
            for s in it.strokes:
                pts = s.get("points", [])
                pieces = self._split_stroke_by_eraser(pts, local_pt, radius)
                if len(pieces) != 1 or pieces[0] is not pts:
                    changed = True
                for piece in pieces:
                    if len(piece) >= 2:
                        new_strokes.append({
                            "color": s.get("color", "#ffffff"),
                            "width": s.get("width", 3),
                            "points": piece,
                        })
            if changed:
                it.prepareGeometryChange()
                it.strokes = new_strokes
                if not it.strokes:
                    self.removeItem(it)
                else:
                    it.update()

    @staticmethod
    def _split_stroke_by_eraser(points, center, radius):
        """Cut `points` (a stroke's polyline, in the item's own local
        coordinates) into however many pieces remain once every point
        within `radius` of `center` is removed. Returns [points]
        unchanged (same list object) if nothing was actually touched, so
        the caller can cheaply tell whether anything changed."""
        if not points:
            return [points]
        r2 = radius * radius
        pieces = []
        current = []
        touched = False
        for p in points:
            dx, dy = p[0] - center.x(), p[1] - center.y()
            if dx * dx + dy * dy <= r2:
                touched = True
                if len(current) >= 2:
                    pieces.append(current)
                current = []
            else:
                current.append(p)
        if len(current) >= 2:
            pieces.append(current)
        if not touched:
            return [points]
        return pieces

    def mousePressEvent(self, event):
        if self.draw_mode and self.erase_mode and event.button() == Qt.LeftButton:
            self._erasing = True
            self._erase_at(event.scenePos())
            event.accept()
            return
        if self.draw_mode and event.button() == Qt.LeftButton:
            pos = event.scenePos()
            self._current_stroke_points = [pos]
            self._current_preview_item = QGraphicsPathItem()
            self._current_preview_item.setPen(self._make_pen())
            self._current_preview_item.setZValue(9999)
            if len(self._current_stroke_points) > 1:
                path = QPainterPath()
                path.moveTo(self._current_stroke_points[0])
                for p in self._current_stroke_points[1:]:
                    path.lineTo(p)
                self._current_preview_item.setPath(path)
            self.addItem(self._current_preview_item)
            event.accept()
            return
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if self.draw_mode and self.erase_mode and self._erasing:
            self._erase_at(event.scenePos())
            event.accept()
            return
        if self.draw_mode and self._current_preview_item is not None:
            self._current_stroke_points.append(event.scenePos())
            path = QPainterPath()
            path.moveTo(self._current_stroke_points[0])
            for p in self._current_stroke_points[1:]:
                path.lineTo(p)
            self._current_preview_item.setPath(path)
            event.accept()
            return
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        if self.draw_mode and self.erase_mode:
            self._erasing = False
            event.accept()
            return
        if self.draw_mode and self._current_preview_item is not None:
            pts = self._current_stroke_points
            self.removeItem(self._current_preview_item)
            self._current_preview_item = None
            if len(pts) >= 2:
                xs = [p.x() for p in pts]
                ys = [p.y() for p in pts]
                pad = self._effective_width() + 6
                x0, y0 = min(xs) - pad, min(ys) - pad
                w = (max(xs) - min(xs)) + pad * 2
                h = (max(ys) - min(ys)) + pad * 2
                rel_points = [[p.x() - x0, p.y() - y0] for p in pts]
                item = DrawingItem(
                    x0, y0, w, h,
                    strokes=[{
                        "color": self._stroke_color().name(QColor.HexArgb),
                        "width": self._effective_width(),
                        "points": rel_points,
                    }],
                )
                self.addItem(item)
                self.bring_to_front(item)
            self._current_stroke_points = []
            event.accept()
            return
        super().mouseReleaseEvent(event)

    # -- rectangular multi-select of several drawings -> treat as one ---
    def merge_selected_drawings(self):
        """When a rubber-band (rectangular) selection catches more than one
        DrawingItem, combine them into a single DrawingItem instead of
        leaving them as separate objects. This replaces the old
        "guess which stroke is closest and auto-merge while drawing"
        heuristic with an explicit, predictable action the user
        triggers by selecting multiple sketches at once."""
        drawings = [it for it in self.selectedItems() if isinstance(it, DrawingItem)]
        if len(drawings) < 2:
            return None
        xs0, ys0, xs1, ys1 = [], [], [], []
        for it in drawings:
            xs0.append(it.pos().x())
            ys0.append(it.pos().y())
            xs1.append(it.pos().x() + it._w)
            ys1.append(it.pos().y() + it._h)
        x0, y0 = min(xs0), min(ys0)
        w = max(1.0, max(xs1) - x0)
        h = max(1.0, max(ys1) - y0)
        merged_strokes = []
        for it in drawings:
            dx = it.pos().x() - x0
            dy = it.pos().y() - y0
            for s in it.strokes:
                merged_strokes.append({
                    "color": s.get("color", "#ffffff"),
                    "width": s.get("width", 3),
                    "points": [[p[0] + dx, p[1] + dy] for p in s.get("points", [])],
                })
        for it in drawings:
            self.removeItem(it)
        merged = DrawingItem(x0, y0, w, h, strokes=merged_strokes)
        self.addItem(merged)
        self.bring_to_front(merged)
        self.clearSelection()
        merged.setSelected(True)
        return merged

    # -- drag a component onto a board card to nest it -----------------
    def item_drag_released(self, item, hover_board=None):
        if isinstance(item, BoardCardItem):
            return
        if isinstance(item, DrawingItem) and not item.allow_board_card:
            # Mirrors _update_board_hover_preview's own refusal above -
            # without this, a sketch dropped squarely on a card while
            # its preview line simply never appeared would still have
            # silently nested itself here anyway.
            return
        other = hover_board if (hover_board is not None and hover_board.scene() is self) else None
        if other is None:
            # Fallback for callers that don't track hover state themselves
            # (e.g. programmatic calls) - re-detect via the item's own
            # center, same as before.
            try:
                center = item.mapToScene(item.rect().center())
            except Exception:
                return
            for cand in self.items(center):
                if isinstance(cand, BoardCardItem) and cand is not item:
                    other = cand
                    break
        if other is not None:
            sub = component_to_subitem(item)
            if sub is not None:
                # Insert at the slot the user was hovering over (shown
                # live by the insertion preview line) rather than
                # recomputing it from the dragged item's own center,
                # which for a tall/long item can sit well outside the
                # board card even while the cursor - and the preview
                # line - were correctly over its bottom edge.
                local_y = other._insert_preview_y
                if local_y is None:
                    center = item.mapToScene(item.rect().center())
                    local_y = other.mapFromScene(center).y()
                idx = other._subitem_insert_index(local_y)
                other.add_subitem(sub, index=idx)
                other.clear_insert_preview()
                self.removeItem(item)

    # -- helpers ----------------------------------------------------------
    def all_component_items(self):
        return [it for it in self.items() if isinstance(it, BaseComponentItem)]

    def serialize(self):
        # Sorted by id (a fixed, stable identifier - see
        # BaseComponentItem.__init__/new_id()) rather than left in
        # self.items()'s own traversal order: that order is Qt's current
        # stacking order, and for two items that happen to share the
        # same zValue(), its tie-break isn't guaranteed to stay fixed
        # across calls - it can shift once Qt's internal scene index
        # gets rebuilt, which the very first repaint after a board loads
        # is enough to trigger. Since z-order is already captured
        # per-item in each dict's own "z" field, this list's ordering
        # carries no meaning of its own - but leaving it unstable meant
        # two JSON snapshots of the exact same, entirely unedited board
        # could still come out different purely because of *when* they
        # were taken, which is what made _has_unsaved_changes() keep
        # reporting phantom changes and prompting to save after every
        # single navigation, whether anything was actually edited or not.
        items = sorted(self.all_component_items(), key=lambda it: it.id)
        return {"items": [it.serialize() for it in items]}

    def clear_board(self):
        # Drop selection/focus up front, before anything is actually
        # removed: with nothing selected/focused, removing an item never
        # has to shrink a *live* selection or move focus off a component
        # that's about to be destroyed, which is what fired
        # selectionChanged/focusItemChanged (and every handler hanging
        # off them, in MainWindow and elsewhere) once per removed item,
        # mid-teardown, on an already-partially-cleared scene - the
        # main source of the crash-on-navigate-away bug (see
        # MainWindow._load_board_file, which additionally resets its
        # own stale item references before calling here).
        _debug_perf_snapshot("clear_board: before teardown")
        self.clearFocus()
        self.clearSelection()
        # weakref, not a plain list: a normal list of the items here would
        # itself keep every one of them alive for as long as this list is
        # in scope, which would make the leak-detection snapshots below
        # always report "still referenced" even when nothing is actually
        # wrong - the whole point is to observe what's left over once
        # *this* function's own references are gone too.
        _wrefs = [weakref.ref(it) for it in self.all_component_items()]
        for wr in _wrefs:
            it = wr()
            if it is not None:
                self.removeItem(it)
        it = None
        _debug_perf_snapshot("clear_board: after removeItem, before gc")
        if _PERF_DEBUG:
            gc.collect()
            reported_types = set()
            for wr in _wrefs:
                obj = wr()
                if obj is not None and type(obj) not in reported_types:
                    reported_types.add(type(obj))
                    _debug_describe_referrers(obj)
            obj = None
        _wrefs = None
        # MindMapView._grow_scene_rect_if_needed() only ever grows
        # sceneRect (see its own docstring) and this same MindMapScene
        # instance is reused for every board opened in the session - so
        # without resetting it here, panning/zooming around on ANY
        # board (including one you've since navigated away from) left
        # sceneRect permanently bloated for every board opened
        # afterwards too. A huge sceneRect means a correspondingly huge
        # internal spatial index (Qt's BSP tree, which is what panning/
        # zoom's visible-item culling relies on), which is why panning
        # and zooming kept getting more sluggish the more boards you
        # visited in one sitting - and, combined with a GPU-backed
        # QOpenGLWidget viewport and per-item DeviceCoordinateCache, is
        # also a very plausible route to the degenerate (zero/garbage
        # size) paint-device cache states seen at extreme zoom-out.
        # Resetting back to the same default MindMapScene.__init__()
        # starts with means each newly loaded board's viewport/scrollbar
        # geometry is only ever grown from its own actual content again.
        self.setSceneRect(-5000, -5000, 10000, 10000)
        if _PERF_DEBUG:
            _debug_perf_snapshot("clear_board: after sceneRect reset (should show 0 items if nothing leaked)")

    def load(self, data, progress_callback=None):
        """progress_callback(done, total), if given, is called after each
        item is deserialized/added - used by MainWindow to drive the
        bottom-left "Loading <board>... N%" status label while opening or
        navigating to a board (see MainWindow._load_board_file). total is
        the item count up front, so callers can turn it straight into a
        percentage without tracking anything themselves."""
        self.clear_board()
        items = []
        item_dicts = data.get("items", [])
        total = len(item_dicts)
        for i, d in enumerate(item_dicts, 1):
            item = deserialize_component(d)
            if item:
                self.addItem(item)
                items.append(item)
            if progress_callback is not None:
                progress_callback(i, total)
        id_map = {it.id: it for it in items}
        for it in items:
            if isinstance(it, ArrowItem):
                it.resolve_pending_anchors(id_map)
        # A board saved by an older version stored arrows with the old
        # always-on-top z-values (see ARROW_Z_OFFSET) baked right into
        # the file - loading them as-is would keep those stale z-values
        # forever, since nothing here calls bring_to_front() on load.
        # Re-sorting every loaded arrow into today's below-components
        # band (while preserving their relative order to each other)
        # means an old save immediately renders arrows behind the
        # components they connect, matching a freshly-drawn arrow,
        # without waiting for the user to click each one individually.
        arrow_items = sorted(
            (it for it in items if isinstance(it, ArrowItem)), key=lambda it: it.zValue()
        )
        for i, it in enumerate(arrow_items):
            it.setZValue(ARROW_Z_OFFSET + i)
        _debug_perf_snapshot(f"load(): after adding {len(items)} items from file")


# --------------------------------------------------------------------------
# View (canvas): middle-mouse panning, ctrl+wheel zoom, OS file drop
# --------------------------------------------------------------------------

class MindMapView(QGraphicsView):
    # The scene's own sceneRect() is what QGraphicsView derives its
    # scrollbar range from, and a fixed one (the original board was
    # created with a flat -5000,-5000,10000,10000) is a real, reachable
    # wall - pan far enough in any direction and the scrollbar simply
    # runs out of room, which is exactly the "panning stops and I can't
    # go further" bug. There's no such thing as an actually-infinite
    # QRectF (Qt's coordinates are still plain floats), so instead this
    # keeps growing the scene rect on demand, in whatever direction the
    # user is heading, well before they can ever reach its current edge
    # - see _grow_scene_rect_if_needed, called after every pan, zoom,
    # and viewport resize. In practice the usable area ends up far
    # larger than anyone would ever pan a mind-map board across.
    SCENE_RECT_MARGIN = 4000  # once the visible area gets within this many
                               # scene units of sceneRect()'s current edge,
                               # push that edge further out
    SCENE_RECT_GROW = 20000   # how far each growth step pushes the edge -
                               # large relative to MARGIN so this doesn't
                               # keep re-triggering on every small pan

    def __init__(self, scene, main_window, parent=None):
        super().__init__(scene, parent)
        self.main_window = main_window
        self.setRenderHints(QPainter.Antialiasing | QPainter.SmoothPixmapTransform)
        if HAS_OPENGL:
            self.setViewport(QOpenGLWidget())
        self.setCacheMode(QGraphicsView.CacheBackground)
        self.setDragMode(QGraphicsView.RubberBandDrag)
        self.setAcceptDrops(True)
        self.setTransformationAnchor(QGraphicsView.AnchorUnderMouse)
        self.setResizeAnchor(QGraphicsView.AnchorUnderMouse)
        self._panning = False
        self._pan_start = QPoint()
        self._growing_scene_rect = False

    def _grow_scene_rect_if_needed(self):
        scene = self.scene()
        if scene is None or self._growing_scene_rect:
            return
        viewport_rect = self.viewport().rect()
        if not viewport_rect.isValid():
            return
        visible = self.mapToScene(viewport_rect).boundingRect()
        rect = scene.sceneRect()
        left, top = rect.left(), rect.top()
        right, bottom = rect.right(), rect.bottom()
        grew = False
        if visible.left() - left < self.SCENE_RECT_MARGIN:
            left -= self.SCENE_RECT_GROW
            grew = True
        if right - visible.right() < self.SCENE_RECT_MARGIN:
            right += self.SCENE_RECT_GROW
            grew = True
        if visible.top() - top < self.SCENE_RECT_MARGIN:
            top -= self.SCENE_RECT_GROW
            grew = True
        if bottom - visible.bottom() < self.SCENE_RECT_MARGIN:
            bottom += self.SCENE_RECT_GROW
            grew = True
        if not grew:
            return
        # setSceneRect() recalculates the scrollbar ranges, which fires
        # scrollContentsBy() again (see below) - guarded so that nested
        # call finds nothing left to grow and just returns instead of
        # recursing.
        self._growing_scene_rect = True
        try:
            scene.setSceneRect(left, top, right - left, bottom - top)
            if _PERF_DEBUG:
                r = scene.sceneRect()
                print(f"[PERF] sceneRect grew to {r.width():.0f}x{r.height():.0f} "
                      f"(area={r.width() * r.height():.3e})", file=sys.stderr)
        finally:
            self._growing_scene_rect = False

    def scrollContentsBy(self, dx, dy):
        super().scrollContentsBy(dx, dy)
        self._grow_scene_rect_if_needed()

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self._grow_scene_rect_if_needed()

    def showEvent(self, event):
        super().showEvent(event)
        self._grow_scene_rect_if_needed()

    def wheelEvent(self, event):
        if event.modifiers() & Qt.ControlModifier:
            factor = 1.15 if event.angleDelta().y() > 0 else 1 / 1.15
            self.scale(factor, factor)
            self._grow_scene_rect_if_needed()
            self.main_window._update_zoom_label()
        else:
            super().wheelEvent(event)

    # -- view state (zoom/pan) persistence --------------------------------
    # Saved with the board so the read-only HTML export can open framed
    # exactly as it was left in the editor, instead of always re-fitting
    # to content from scratch on its own - which usually lands on a
    # different zoom/pan than whatever the user was actually looking at
    # when they hit Save, making the two views look like they disagree
    # about where things are even though the underlying coordinates match.
    def current_view_state(self):
        center = self.mapToScene(self.viewport().rect().center())
        return {"scale": self.transform().m11(), "center_x": center.x(), "center_y": center.y()}

    def apply_view_state(self, state):
        if not state:
            return
        scale = state.get("scale")
        if scale:
            self.resetTransform()
            self.scale(scale, scale)
            self.main_window._update_zoom_label()
        cx, cy = state.get("center_x"), state.get("center_y")
        if cx is not None and cy is not None:
            self.centerOn(cx, cy)

    def mousePressEvent(self, event):
        # A press anywhere deselects whichever Board Card subitem was
        # single-click "selected" (see MindMapScene.select_board_subitem)
        # - if this same press turns out to land on a subitem again (the
        # same one, a different one, or one in a different card),
        # BoardCardItem.mouseReleaseEvent below re-selects it right
        # after; if it lands anywhere else entirely, it simply stays
        # cleared, exactly like clicking away from a normally-selected
        # component.
        self.scene().clear_board_subitem_selection()
        if event.button() == Qt.MiddleButton:
            self._panning = True
            self._pan_start = event.position().toPoint()
            self.setCursor(Qt.ClosedHandCursor)
            event.accept()
            return
        # Flagged for the whole press-to-release span whenever a left
        # click could start a rubber-band drag-select, even though a
        # click straight onto an item ends up just selecting/dragging it
        # instead - harmless either way, since mouseReleaseEvent always
        # clears the flag and runs one real selection-sync pass right
        # after, so the only effect on a plain click is that sync moving
        # from press to release (imperceptible). See
        # MindMapScene.rubber_band_dragging for why this exists.
        if event.button() == Qt.LeftButton and self.dragMode() == QGraphicsView.RubberBandDrag:
            self.scene().rubber_band_dragging = True
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if self._panning:
            delta = event.position().toPoint() - self._pan_start
            self._pan_start = event.position().toPoint()
            hbar = self.horizontalScrollBar()
            vbar = self.verticalScrollBar()
            hbar.setValue(hbar.value() - delta.x())
            vbar.setValue(vbar.value() - delta.y())
            event.accept()
            return
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        if event.button() == Qt.MiddleButton and self._panning:
            self._panning = False
            self.setCursor(Qt.ArrowCursor)
            event.accept()
            return
        was_rubber_band = (
            event.button() == Qt.LeftButton and self.dragMode() == QGraphicsView.RubberBandDrag
        )
        super().mouseReleaseEvent(event)
        if was_rubber_band:
            scene = self.scene()
            scene.rubber_band_dragging = False
            # Run the (deliberately skipped mid-drag - see
            # MindMapScene.rubber_band_dragging) selection-sync handlers
            # once for real now that the drag is actually over, so the
            # toolbar/anchor-markers/undo-checkpoint all end up correct
            # no matter how many selectionChanged emissions were
            # swallowed while dragging.
            scene.update_anchor_endpoint_markers()
            self.main_window.on_selection_changed()
            self.main_window._flush_pending_undo_checkpoint()
            # A rectangular selection just finished: if it caught more than
            # one freehand drawing, treat them as a single object from now
            # on (instead of the old nearest-object-guessing merge).
            scene.merge_selected_drawings()

    def dragEnterEvent(self, event):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()
        else:
            super().dragEnterEvent(event)

    def dragMoveEvent(self, event):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()
        else:
            super().dragMoveEvent(event)

    def dropEvent(self, event):
        if event.mimeData().hasUrls():
            pos = event.position().toPoint() if hasattr(event, "position") else event.pos()
            scene_pos = self.mapToScene(pos)
            target = self.itemAt(pos)
            comp = target
            while comp is not None and not isinstance(comp, BaseComponentItem):
                comp = comp.parentItem()
            if isinstance(comp, (ImageItem, GifItem, VideoItem, BoardCardItem)):
                comp.dropEvent(event)
                event.acceptProposedAction()
                return
            # A dropped .html file is a board, not a media file to embed -
            # open it the same way File > Open... would, rather than
            # falling through to create_item_from_file (which would just
            # reject it as an unsupported type).
            html_path = None
            for url in event.mimeData().urls():
                p = url.toLocalFile()
                if p.lower().endswith(".html"):
                    html_path = p
                    break
            if html_path is not None:
                event.acceptProposedAction()
                self.main_window.open_dropped_board(html_path)
                return
            for url in event.mimeData().urls():
                path = url.toLocalFile()
                self.main_window.create_item_from_file(path, scene_pos)
            event.acceptProposedAction()
        else:
            super().dropEvent(event)


# --------------------------------------------------------------------------
# HTML export / import
# --------------------------------------------------------------------------

HTML_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<title>OpenNote Export</title>
<style>
  html,body {{ margin:0; padding:0; background:#141414; overflow:hidden; font-family:'Segoe UI',Arial,sans-serif; height:100%; }}
  #viewport {{ width:100%; height:100vh; overflow:hidden; position:relative; cursor:grab; }}
  body.has-breadcrumb #viewport {{ height:calc(100vh - 37px); margin-top:37px; }}
  #canvas {{ position:absolute; top:0; left:0; transform-origin:0 0; }}
  .comp {{ position:absolute; box-sizing:border-box; }}
  .text-note {{ border-radius:8px; padding:10px; color:#e8e8e8; box-shadow:0 2px 6px rgba(0,0,0,.4); white-space:pre-wrap; overflow:auto; }}
  .plain-text-note {{ padding:4px; white-space:pre-wrap; overflow:auto; font-size:15px; }}
  .image-note, .gif-note, .video-note {{ display:flex; flex-direction:column; background:#111; border:1px solid #000; box-sizing:border-box; }}
  .image-note img, .gif-note img {{ flex:1 1 auto; width:100%; min-height:0; object-fit:contain; background:#111; }}
  .video-note video {{ flex:1 1 auto; width:100%; min-height:0; background:#000; }}
  .media-title {{ flex:0 0 auto; background:#1e1e1e; color:#fff; font-weight:600; font-size:13px; padding:4px 8px; }}
  .media-desc {{ flex:0 0 auto; background:#1e1e1e; color:#aaa; font-size:12px; padding:4px 8px; }}
  .drawing-note svg {{ width:100%; height:100%; }}
  .arrow-note svg {{ width:100%; height:100%; }}
  .board-card {{ background:#2b2b2b; border-radius:10px; border:1px solid #111; color:#eee; overflow:hidden; box-shadow:0 4px 10px rgba(0,0,0,.5); }}
  .board-title {{ background:#1e1e1e; padding:8px 12px; font-weight:600; }}
  /* height:auto (not a fixed calc(100% - 40px)) so the body always grows
     to fit its actual rendered content. The browser's layout engine
     (natural img aspect-ratio, its own font metrics for wrapped text)
     essentially never reproduces Qt's paint()-computed row heights to
     the pixel, so a fixed height + overflow:auto here would just hide
     that mismatch behind a scrollbar instead of the card visually
     "autogrowing" the way it does live in the app - see
     BoardCardItem.to_html(), which sets min-height (not height) on the
     card itself for the same reason. */
  .board-body {{ padding:8px; overflow:visible; height:auto; }}
  .sub-image, .sub-video {{ margin-bottom:18px; border-radius:4px; overflow:hidden; background:#111; }}
  .sub-image img {{ width:100%; display:block; }}
  .sub-video video {{ width:100%; display:block; }}
  .sub-image .media-title, .sub-video .media-title {{ font-size:12px; padding:4px 8px; }}
  .sub-image .media-desc, .sub-video .media-desc {{ font-size:11px; padding:4px 8px; }}
  .sub-text {{ margin-bottom:8px; font-size:13px; color:#ddd; }}
  .sub-checklist {{ list-style:none; padding:0; margin:0 0 8px 0; font-size:13px; color:#ddd; }}
  .sub-checklist li {{ margin-bottom:4px; }}
  .board-link-card {{ display:flex; flex-direction:column; justify-content:flex-end; background:#233047; border:1px solid #111; border-radius:10px; color:#eee; padding:12px; box-shadow:0 4px 10px rgba(0,0,0,.5); text-decoration:none; box-sizing:border-box; overflow:hidden; }}
  .board-link-thumb {{ display:block; flex:0 0 auto; width:calc(100% + 24px); height:55%; object-fit:cover; margin:-12px -12px 8px -12px; }}
  .board-link-title {{ font-weight:700; font-size:15px; color:#fff; }}
  .board-link-sub {{ font-size:11px; color:#9aa4b2; margin-top:4px; }}
  .board-link-desc {{ font-size:13px; color:#e8e8e8; margin-top:8px; padding-top:8px; border-top:1px solid rgba(255,255,255,.16); white-space:pre-wrap; word-break:break-word; }}
  #breadcrumb {{ position:fixed; top:0; left:0; right:0; z-index:20; background:#1b1b1b; border-bottom:1px solid #000; padding:8px 14px; font-size:13px; color:#aaa; }}
  #breadcrumb a {{ color:#8ab4ff; text-decoration:none; }}
  #breadcrumb a:hover {{ text-decoration:underline; }}
  #breadcrumb .crumb-sep {{ margin:0 6px; color:#555; }}
  #breadcrumb .crumb-current {{ color:#eee; font-weight:600; }}
  #hint {{ position:fixed; bottom:10px; left:10px; color:#888; font-size:12px; z-index:10; }}
</style>
</head>
<body>
{breadcrumb_html}
<div id="viewport">
  <div id="canvas">
    {components}
  </div>
</div>
<div id="hint">Read-only view &mdash; scroll to zoom, drag to pan. Open with the OpenNote app to edit.</div>
<script type="application/json" id="mindmap-meta">{meta_json}</script>
<script type="application/json" id="mindmap-data">{json_data}</script>
<script>
(function() {{
  var viewport = document.getElementById('viewport');
  var canvas = document.getElementById('canvas');
  var bounds = {bounds_json};
  var savedView = {view_json};
  var scale = 1, originX = 60, originY = 60;
  var isPanning = false, startX = 0, startY = 0;

  function apply() {{
    canvas.style.transform = 'translate(' + originX + 'px,' + originY + 'px) scale(' + scale + ')';
  }}

  // Fit the initial view to where the content actually is, instead of
  // always starting at scale=1 / origin=(60,60) - which, for boards whose
  // items live far from (0,0) in scene coordinates, left the viewer
  // looking at an empty patch of canvas until they panned around.
  function fitToContent() {{
    var vw = viewport.clientWidth || window.innerWidth;
    var vh = viewport.clientHeight || window.innerHeight;
    var bw = Math.max(1, bounds.x1 - bounds.x0);
    var bh = Math.max(1, bounds.y1 - bounds.y0);
    var pad = 60;
    scale = Math.min((vw - pad * 2) / bw, (vh - pad * 2) / bh, 1.5);
    scale = Math.max(0.05, scale);
    originX = (vw - bw * scale) / 2 - bounds.x0 * scale;
    originY = (vh - bh * scale) / 2 - bounds.y0 * scale;
    apply();
  }}

  // Reopen the board framed exactly as it was left in the editor when it
  // was saved (same zoom, same point centered) instead of always
  // re-fitting to content from scratch - the two used to disagree on
  // where things appeared on screen simply because they were computing
  // two different views of the same coordinates.
  function applySavedView() {{
    var vw = viewport.clientWidth || window.innerWidth;
    var vh = viewport.clientHeight || window.innerHeight;
    scale = savedView.scale;
    originX = vw / 2 - savedView.center_x * scale;
    originY = vh / 2 - savedView.center_y * scale;
    apply();
  }}

  function fitInitialView() {{
    if (savedView && savedView.scale) {{
      applySavedView();
    }} else {{
      fitToContent();
    }}
  }}

  viewport.addEventListener('wheel', function(e) {{
    e.preventDefault();
    // Zoom anchored on the mouse cursor: convert the cursor's current
    // screen position into canvas-space (scene) coordinates *before*
    // changing scale, then re-solve originX/originY so that same
    // canvas-space point stays under the cursor afterwards. Previously
    // this only changed `scale` and left originX/originY untouched -
    // since the transform is translate(originX,originY) scale(scale)
    // with transform-origin:0 0, that meant canvas-space point (0,0)
    // always stayed pinned to whatever screen position originX/originY
    // happened to be, so zooming always anchored on that one fixed
    // point instead of wherever the cursor (and the view, after
    // panning) actually was.
    var rect = viewport.getBoundingClientRect();
    var mouseX = e.clientX - rect.left;
    var mouseY = e.clientY - rect.top;
    var canvasX = (mouseX - originX) / scale;
    var canvasY = (mouseY - originY) / scale;
    var delta = e.deltaY < 0 ? 1.1 : 0.9;
    scale = Math.min(4, Math.max(0.15, scale * delta));
    originX = mouseX - canvasX * scale;
    originY = mouseY - canvasY * scale;
    apply();
  }}, {{ passive:false }});

  viewport.addEventListener('mousedown', function(e) {{
    isPanning = true; startX = e.clientX - originX; startY = e.clientY - originY;
    viewport.style.cursor = 'grabbing';
  }});
  window.addEventListener('mousemove', function(e) {{
    if (!isPanning) return;
    originX = e.clientX - startX; originY = e.clientY - startY;
    apply();
  }});
  window.addEventListener('mouseup', function() {{
    isPanning = false; viewport.style.cursor = 'grab';
  }});
  window.addEventListener('resize', fitInitialView);

  fitInitialView();

  // --- Snapped-arrow correction ------------------------------------
  // Every arrow's p1/p2 baked into its <svg> were computed against the
  // *Qt* size of whatever it's anchored to (see ArrowItem.to_html() in
  // the app). A card's actual rendered box in a browser can come out a
  // different size than it was in Qt - most visibly board-card, whose
  // CSS uses min-height (not height) so it can auto-grow to fit real
  // browser font metrics (see the .board-body CSS comment above). When
  // that happens the baked anchor point no longer sits on the card's
  // true on-screen border/center, and a "snapped" arrow visibly drifts
  // off the card it's supposed to be attached to.
  //
  // This pass re-derives each anchored endpoint from the target's
  // *actual* rendered box (offsetLeft/Top/Width/Height - these are
  // plain unscaled canvas-space pixels, unaffected by the pan/zoom
  // transform on #canvas, since that transform is purely visual) using
  // the same rx/ry border fraction (or dead-center, for a headless end)
  // the app itself computed, then redraws that arrow's line/head(s)/
  // label to match - so the exported page self-corrects regardless of
  // any Qt-vs-browser layout difference, instead of trusting numbers
  // that were only ever true back in the app.
  try {{
    var mmDataEl = document.getElementById('mindmap-data');
    var mmData = mmDataEl ? JSON.parse(mmDataEl.textContent) : null;
    var items = (mmData && mmData.items) || [];
    var byId = {{}};
    document.querySelectorAll('.comp[data-id]').forEach(function(el) {{
      byId[el.getAttribute('data-id')] = el;
    }});

    function endpointHasHead(style, which) {{
      if (which === 2) return style === 'single' || style === 'double';
      return style === 'double';
    }}

    // Mirrors ArrowItem.to_html()'s head_polygon()/dasharray/trim math.
    function buildArrowSvg(d, p1, p2) {{
      var dx = p2.x - p1.x, dy = p2.y - p1.y;
      var length = Math.max(0.0001, Math.hypot(dx, dy));
      var ux = dx / length, uy = dy / length;
      var strokeWidth = d.stroke_width || 4;
      var size = Math.max(8, strokeWidth * 3);
      var spread = 28 * Math.PI / 180;
      var color = d.color || '#ffffff';

      function headPolygon(tipX, tipY, dirx, diry) {{
        var angle = Math.atan2(diry, dirx);
        var lx = tipX - size * Math.cos(angle - spread);
        var ly = tipY - size * Math.sin(angle - spread);
        var rx = tipX - size * Math.cos(angle + spread);
        var ry = tipY - size * Math.sin(angle + spread);
        return tipX.toFixed(1) + ',' + tipY.toFixed(1) + ' ' +
               lx.toFixed(1) + ',' + ly.toFixed(1) + ' ' +
               rx.toFixed(1) + ',' + ry.toFixed(1);
      }}

      var back = size * Math.cos(spread);
      var lp1x = p1.x, lp1y = p1.y, lp2x = p2.x, lp2y = p2.y;
      if (d.style === 'double') {{
        var b = Math.min(back, length * 0.45);
        lp1x = p1.x + ux * b; lp1y = p1.y + uy * b;
        lp2x = p2.x - ux * b; lp2y = p2.y - uy * b;
      }} else if (d.style === 'single') {{
        var b2 = Math.min(back, length * 0.9);
        lp2x = p2.x - ux * b2; lp2y = p2.y - uy * b2;
      }}

      var heads = '';
      if (d.style === 'single' || d.style === 'double') {{
        heads += '<polygon points="' + headPolygon(p2.x, p2.y, ux, uy) + '" fill="' + color + '"/>';
      }}
      if (d.style === 'double') {{
        heads += '<polygon points="' + headPolygon(p1.x, p1.y, -ux, -uy) + '" fill="' + color + '"/>';
      }}
      var dashAttr = '';
      if (d.line_style === 'dashed') {{
        dashAttr = ' stroke-dasharray="' + (strokeWidth * 2.5).toFixed(1) + ',' + (strokeWidth * 1.5).toFixed(1) + '"';
      }} else if (d.line_style === 'dashdot') {{
        dashAttr = ' stroke-dasharray="' + (strokeWidth * 2.5).toFixed(1) + ',' + (strokeWidth * 1.3).toFixed(1) +
                   ',' + (strokeWidth * 0.6).toFixed(1) + ',' + (strokeWidth * 1.3).toFixed(1) + '"';
      }}
      return '<line x1="' + lp1x.toFixed(1) + '" y1="' + lp1y.toFixed(1) + '" x2="' + lp2x.toFixed(1) +
             '" y2="' + lp2y.toFixed(1) + '" stroke="' + color + '" stroke-width="' + strokeWidth +
             '" stroke-linecap="square"' + dashAttr + '/>' + heads;
    }}

    items.forEach(function(d) {{
      if (d.type !== 'arrow' || (!d.anchor1 && !d.anchor2)) return;
      var arrowEl = byId[d.id];
      if (!arrowEl) return;
      var svg = arrowEl.querySelector('svg');
      if (!svg) return;

      // Local (arrow-relative) points, defaulting to whatever was baked
      // in - only overwritten below for an end that's actually anchored
      // *and* whose target we can actually find in this document.
      var p1 = {{ x: (d.p1 && d.p1[0]) || 0, y: (d.p1 && d.p1[1]) || 0 }};
      var p2 = {{ x: (d.p2 && d.p2[0]) || 0, y: (d.p2 && d.p2[1]) || 0 }};
      var changed = false;

      [[d.anchor1, 1], [d.anchor2, 2]].forEach(function(pair) {{
        var anchor = pair[0], which = pair[1];
        if (!anchor) return;
        var targetEl = byId[anchor.item_id];
        if (!targetEl) return;
        var tLeft = targetEl.offsetLeft, tTop = targetEl.offsetTop;
        var tW = targetEl.offsetWidth, tH = targetEl.offsetHeight;
        var scenePt;
        if (endpointHasHead(d.style, which)) {{
          scenePt = {{ x: tLeft + anchor.rx * tW, y: tTop + anchor.ry * tH }};
        }} else {{
          scenePt = {{ x: tLeft + tW / 2, y: tTop + tH / 2 }};
        }}
        var local = {{ x: scenePt.x - d.x, y: scenePt.y - d.y }};
        if (which === 1) {{ p1 = local; }} else {{ p2 = local; }}
        changed = true;
      }});

      if (changed) {{
        svg.innerHTML = buildArrowSvg(d, p1, p2);
        var labelEl = arrowEl.querySelector('.arrow-label');
        if (labelEl) {{
          var midX = (p1.x + p2.x) / 2, midY = (p1.y + p2.y) / 2;
          labelEl.style.left = midX + 'px';
          labelEl.style.top = midY + 'px';
        }}
      }}
    }});
  }} catch (e) {{
    // Anchor correction is a best-effort visual touch-up; if anything
    // above goes wrong, fall back silently to the baked-in geometry
    // rather than breaking the rest of the exported page.
    console.warn('Snapped-arrow correction skipped:', e);
  }}
}})();
</script>
</body>
</html>
"""


def build_html_document(data):
    comps_html = []
    xs0, ys0, xs1, ys1 = [], [], [], []
    # Render components in ascending z-order (lowest first) so the DOM
    # order alone reproduces the same stacking as the app - browsers
    # paint later-in-DOM elements on top of earlier ones by default (no
    # z-index needed), so the item with the highest zValue() simply needs
    # to be the LAST <div> emitted. Without this, exported HTML always
    # stacked components in whatever order they happened to appear in
    # `data["items"]`, ignoring each component's actual z position (e.g.
    # an Arrow brought to front in the app, or any component moved/
    # clicked to raise it) - see BaseComponentItem/ArrowItem/BoardCardItem
    # mousePressEvent -> MindMapScene.bring_to_front.
    items_sorted = sorted(data.get("items", []), key=lambda d: d.get("z", 0))
    built_items = []
    for d in items_sorted:
        item = deserialize_component(d)
        if item:
            built_items.append((item, d))
    # Anchored arrow endpoints (self.anchor1/anchor2) only exist as
    # {"item_id","rx","ry"} dicts right after deserialize_component() -
    # resolve_pending_anchors() needs every item to already be built
    # first (an arrow's target may appear later in item order), same as
    # MindMapScene.load() does. Without this, every exported arrow's
    # anchor1/anchor2 stay None, so ArrowItem._render_endpoints() - used
    # by to_html() - never takes the "headless anchored end -> target's
    # own center" branch that paint() takes live in the app, and a
    # snapped endpoint lands on the plain stored border point instead,
    # which is what made snapped arrows drift out of place in the
    # exported HTML.
    id_map = {item.id: item for item, _ in built_items}
    for item, _ in built_items:
        if isinstance(item, ArrowItem):
            item.resolve_pending_anchors(id_map)
    for item, d in built_items:
        comps_html.append(item.to_html())
        x, y = d.get("x", 0), d.get("y", 0)
        w, h = d.get("w", 100), d.get("h", 100)
        xs0.append(x)
        ys0.append(y)
        xs1.append(x + w)
        ys1.append(y + h)
    if xs0:
        bounds = {"x0": min(xs0), "y0": min(ys0), "x1": max(xs1), "y1": max(ys1)}
    else:
        bounds = {"x0": 0, "y0": 0, "x1": 800, "y1": 600}
    json_data = json.dumps(data).replace("</script>", "<\\/script>")
    # Kept separate from json_data (rather than just adding a key to
    # `data` itself) so a reader that only wants this - see
    # BoardLinkItem._refresh_count() - can grab it with a cheap, tiny
    # regex+json.loads instead of having to parse (and, worse, fully
    # decode every embedded image's base64 text inside) the entire,
    # potentially many-megabyte main data blob just to read one number.
    meta_json = json.dumps({"item_count": len(data.get("items", []))})
    bounds_json = json.dumps(bounds)
    view_json = json.dumps(data.get("view"))
    breadcrumb = data.get("breadcrumb") or []
    if breadcrumb:
        parts = []
        for i, seg in enumerate(breadcrumb):
            name = (seg.get("name") or "").replace("&", "&amp;").replace("<", "&lt;")
            is_last = i == len(breadcrumb) - 1
            if i > 0:
                parts.append('<span class="crumb-sep">&rsaquo;</span>')
            if is_last or not seg.get("file"):
                cls = "crumb-current" if is_last else ""
                parts.append(f'<span class="{cls}">{name}</span>')
            else:
                href = seg["file"].replace('"', "&quot;")
                parts.append(f'<a href="{href}">{name}</a>')
        breadcrumb_html = f'<div id="breadcrumb">{"".join(parts)}</div>'
        body_class = ' class="has-breadcrumb"'
    else:
        breadcrumb_html = ""
        body_class = ""
    html = HTML_TEMPLATE.format(
        components="\n".join(comps_html), json_data=json_data, meta_json=meta_json,
        bounds_json=bounds_json, view_json=view_json, breadcrumb_html=breadcrumb_html,
    )
    if body_class:
        html = html.replace("<body>", f"<body{body_class}>", 1)
    return html


def extract_scene_data(html):
    m = re.search(
        r'<script type="application/json" id="mindmap-data">(.*?)</script>',
        html, re.DOTALL,
    )
    if not m:
        return None
    try:
        return json.loads(m.group(1))
    except Exception:
        return None


def _retarget_board_references(data, old_target_file, old_name_no_ext, new_target_file, new_name):
    """Rewrite every board_link item and breadcrumb segment in a single
    board's serialized `data` that still points at `old_target_file` so
    it points at `new_target_file` (and its display name) instead.
    Returns True if anything in `data` was changed. Shared by both
    BoardLinkItem._rename_referenced_board() (renaming a board reached
    via a shortcut card) and MainWindow.rename_main_board() (renaming
    the project's root board), so a rename made either way rewrites
    references identically everywhere."""
    changed = False
    for it in data.get("items", []):
        if it.get("type") == "board_link" and it.get("target_file") == old_target_file:
            it["target_file"] = new_target_file
            if it.get("title") == old_name_no_ext:
                it["title"] = new_name
            changed = True
    for seg in (data.get("breadcrumb") or []):
        if seg.get("file") == old_target_file:
            seg["file"] = new_target_file
            if seg.get("name") == old_name_no_ext:
                seg["name"] = new_name
            changed = True
    return changed


def _apply_rename_to_project_siblings(proj, old_target_file, old_name_no_ext, new_target_file, new_name, skip_path=None):
    """Walk every .html file directly inside project folder `proj` (other
    than `skip_path`, typically the just-renamed file itself, already
    handled by the caller) and rewrite any reference to
    `old_target_file` found in it. Returns how many files were actually
    changed on disk."""
    updated = 0
    skip_norm = os.path.normpath(skip_path) if skip_path else None
    for fname in os.listdir(proj):
        if not fname.lower().endswith(".html"):
            continue
        fpath = os.path.join(proj, fname)
        if skip_norm and os.path.normpath(fpath) == skip_norm:
            continue
        try:
            with open(fpath, "r", encoding="utf-8") as f:
                data = extract_scene_data(f.read())
        except Exception:
            continue
        if data is None:
            continue
        if _retarget_board_references(data, old_target_file, old_name_no_ext, new_target_file, new_name):
            try:
                with open(fpath, "w", encoding="utf-8") as f:
                    f.write(build_html_document(data))
                updated += 1
            except Exception:
                pass
    return updated


def extract_scene_meta(html):
    """The small, cheap-to-parse sibling of extract_scene_data(): reads
    only the lightweight `mindmap-meta` tag (currently just
    {"item_count": N}) a board file was saved with, without going
    anywhere near the (for a photo-heavy board, potentially many
    megabytes of base64-encoded image data) main `mindmap-data` blob.

    Returns None if the tag is missing entirely - true for any board
    saved by a version of the app before this tag existed - so callers
    can fall back to the slower extract_scene_data() just that once."""
    m = re.search(
        r'<script type="application/json" id="mindmap-meta">(.*?)</script>',
        html, re.DOTALL,
    )
    if not m:
        return None
    try:
        return json.loads(m.group(1))
    except Exception:
        return None


# --------------------------------------------------------------------------
# Main window
# --------------------------------------------------------------------------

class _FontFamilyCombo(QFontComboBox):
    """QFontComboBox that always hands text-edit focus back to whatever
    item was being edited once its dropdown closes - whether the user
    picked a new font, re-picked the one already showing, or just hit
    Escape. A plain instance-attribute monkeypatch of hidePopup does NOT
    work for this: closing the popup by clicking an item or pressing
    Escape/Enter happens through Qt's internal C++ call to the virtual
    hidePopup(), which bypasses a Python-side instance attribute -  only
    a real (sub)class override participates in that virtual dispatch."""

    def __init__(self, restore_focus_cb, parent=None):
        super().__init__(parent)
        self._restore_focus_cb = restore_focus_cb

    def hidePopup(self):
        super().hidePopup()
        if self._restore_focus_cb:
            self._restore_focus_cb()


class NumberStepper(QWidget):
    """Compact dark spinbox control that sits next to a QSlider, showing
    its exact current value and letting it be nudged by exactly 1 (the
    stacked up/down arrow buttons) or set directly by typing a number,
    instead of only being draggable on the slider itself."""

    valueChanged = Signal(int)

    def __init__(self, minimum=0, maximum=100, parent=None):
        super().__init__(parent)
        self._min = minimum
        self._max = maximum
        self._value = minimum
        self.setFocusPolicy(Qt.NoFocus)
        self.setObjectName("NumberStepper")
        # Hard-fixed policy: without this, a parent layout with leftover
        # space (like the toolbar here) can stretch this widget wider
        # than its contents, which then get pinned to opposite edges -
        # the number on the left, the arrows way off on the right.
        self.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)

        layout = QHBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        self.edit = QLineEdit()
        self.edit.setAlignment(Qt.AlignCenter)
        self.edit.setValidator(QIntValidator(minimum, maximum, self))
        self.edit.setFixedSize(38, 26)
        self.edit.setFocusPolicy(Qt.ClickFocus)

        # Up/down arrows stacked in their own thin column to the right of
        # the number field, mimicking a native spinbox instead of the
        # previous side-by-side '- [number] +' pill.
        arrows = QWidget()
        arrows.setFixedSize(16, 26)
        arrows_layout = QVBoxLayout(arrows)
        arrows_layout.setContentsMargins(0, 0, 0, 0)
        arrows_layout.setSpacing(0)

        self.up_btn = QPushButton("\u25B2")
        self.down_btn = QPushButton("\u25BC")

        for btn in (self.up_btn, self.down_btn):
            btn.setFixedSize(16, 13)
            # Same NoFocus reasoning as the sliders/color button elsewhere
            # in the toolbar: keeps whatever text item is being edited
            # (e.g. an Arrow's label) from losing focus/edit-mode the
            # instant one of these is clicked.
            btn.setFocusPolicy(Qt.NoFocus)
            btn.setCursor(Qt.PointingHandCursor)
            arrows_layout.addWidget(btn)

        layout.addWidget(self.edit)
        layout.addWidget(arrows)

        self.setStyleSheet("""
            #NumberStepper { background:#2a2a2a; border:1px solid #3d3d3d; border-radius:5px; }
            QLineEdit { background:transparent; color:#eaeaea; border:none; font-size:13px; padding-left:6px; }
            QPushButton { background:#333333; color:#a8a8a8; border:none; font-size:7px; }
            QPushButton:hover { color:#ffffff; background:#3d3d3d; }
            QPushButton:pressed { background:#4a4a4a; }
        """)
        self.up_btn.setStyleSheet(self.up_btn.styleSheet() + "QPushButton { border-top-right-radius:4px; }")
        self.down_btn.setStyleSheet(self.down_btn.styleSheet() + "QPushButton { border-bottom-right-radius:4px; }")

        self.up_btn.clicked.connect(lambda: self.setValue(self._value + 1))
        self.down_btn.clicked.connect(lambda: self.setValue(self._value - 1))
        self.edit.editingFinished.connect(self._on_edit_finished)
        self._sync_text()
        self.setFixedSize(self.edit.width() + arrows.width(), 26)

    def _sync_text(self):
        self.edit.blockSignals(True)
        self.edit.setText(str(self._value))
        self.edit.blockSignals(False)

    def _on_edit_finished(self):
        try:
            v = int(self.edit.text())
        except ValueError:
            v = self._value
        self.setValue(v)

    def setRange(self, minimum, maximum):
        self._min, self._max = minimum, maximum
        self.edit.setValidator(QIntValidator(minimum, maximum, self))
        self.setValue(self._value)

    def value(self):
        return self._value

    def setValue(self, v):
        v = max(self._min, min(self._max, int(round(v))))
        changed = v != self._value
        self._value = v
        self._sync_text()
        if changed:
            self.valueChanged.emit(v)


class PreferencesDialog(QDialog):
    """Settings > Preferences. Two independent things live here:

    1. Defaults for brand-new components (Show Title / Show Description /
       Title Alignment / Font / Title Size / Description Size) - only
       consulted at creation time (see MainWindow._apply_new_component_prefs),
       never retroactive.
    2. "Apply Font to All Components" - the opposite: immediately pushes a
       chosen font onto every existing component, both on the board
       currently open and every other .html board file in the same
       project folder (see MainWindow.apply_font_to_all_boards)."""

    def __init__(self, main_window):
        super().__init__(main_window)
        self.main_window = main_window
        self.setWindowTitle("Preferences")
        self.setMinimumWidth(380)

        layout = QVBoxLayout(self)

        defaults_label = QLabel("New Component Defaults")
        defaults_label.setStyleSheet("font-weight:600;")
        layout.addWidget(defaults_label)

        form = QFormLayout()
        form.setLabelAlignment(Qt.AlignLeft)

        prefs = main_window.prefs
        self.title_checkbox = QCheckBox("Show Title")
        self.title_checkbox.setChecked(bool(prefs.get("default_show_title", True)))
        form.addRow(self.title_checkbox)

        self.desc_checkbox = QCheckBox("Show Description")
        self.desc_checkbox.setChecked(bool(prefs.get("default_show_description", True)))
        form.addRow(self.desc_checkbox)

        self.align_combo = QComboBox()
        for value, label in PREF_ALIGN_OPTIONS:
            self.align_combo.addItem(label, value)
        idx = self.align_combo.findData(prefs.get("default_title_alignment", "left"))
        self.align_combo.setCurrentIndex(max(0, idx))
        form.addRow("Title Alignment:", self.align_combo)

        self.font_combo = QFontComboBox()
        self.font_combo.setCurrentFont(QFont(prefs.get("default_font_family", "Segoe UI")))
        form.addRow("Default Font:", self.font_combo)

        self.title_size_spin = QDoubleSpinBox()
        self.title_size_spin.setRange(4.0, 96.0)
        self.title_size_spin.setDecimals(1)
        self.title_size_spin.setSingleStep(0.5)
        self.title_size_spin.setValue(float(prefs.get("default_title_font_size", 12.0)))
        form.addRow("Default Title Size:", self.title_size_spin)

        self.desc_size_spin = QDoubleSpinBox()
        self.desc_size_spin.setRange(4.0, 96.0)
        self.desc_size_spin.setDecimals(1)
        self.desc_size_spin.setSingleStep(0.5)
        self.desc_size_spin.setValue(float(prefs.get("default_description_font_size", 9.0)))
        form.addRow("Default Description Size:", self.desc_size_spin)

        self.arrow_size_spin = QSpinBox()
        self.arrow_size_spin.setRange(1, 40)
        self.arrow_size_spin.setValue(int(prefs.get("default_arrow_size", 4)))
        form.addRow("Default Arrow Size:", self.arrow_size_spin)

        layout.addLayout(form)

        arrow_snap_label = QLabel("Default Arrow Snapping Method")
        arrow_snap_label.setStyleSheet("font-weight:600; margin-top:8px;")
        layout.addWidget(arrow_snap_label)
        arrow_snap_hint = QLabel(
            "Applies to any component without its own override (set via "
            "that component's right-click menu \u2192 Arrow Snapping)."
        )
        arrow_snap_hint.setWordWrap(True)
        arrow_snap_hint.setStyleSheet("color:#888; font-size:11px;")
        layout.addWidget(arrow_snap_hint)

        self.arrow_snap_group = QButtonGroup(self)
        current_snap_method = prefs.get("default_arrow_snap_method", "orbit")
        for i, (value, label) in enumerate(ARROW_SNAP_METHOD_OPTIONS):
            rb = QRadioButton(label)
            rb.setChecked(current_snap_method == value)
            self.arrow_snap_group.addButton(rb, i)
            layout.addWidget(rb)
        if self.arrow_snap_group.checkedButton() is None:
            first = self.arrow_snap_group.button(0)
            if first is not None:
                first.setChecked(True)

        perf_label = QLabel("Performance")
        perf_label.setStyleSheet("font-weight:600; margin-top:8px;")
        layout.addWidget(perf_label)

        perf_form = QFormLayout()
        perf_form.setLabelAlignment(Qt.AlignLeft)

        self.optimize_grid_checkbox = QCheckBox("Optimize grid rendering")
        self.optimize_grid_checkbox.setToolTip(
            "Skips drawing the background dot grid once you're zoomed out "
            "past the threshold below, instead of rebuilding and redrawing "
            "it on every single frame while panning/zooming."
        )
        self.optimize_grid_checkbox.setChecked(bool(prefs.get("optimize_grid_rendering", True)))
        self.optimize_grid_checkbox.toggled.connect(self._on_optimize_grid_toggled)
        perf_form.addRow(self.optimize_grid_checkbox)

        self.grid_zoom_threshold_spin = QDoubleSpinBox()
        self.grid_zoom_threshold_spin.setRange(1.0, 100.0)
        self.grid_zoom_threshold_spin.setDecimals(0)
        self.grid_zoom_threshold_spin.setSingleStep(5.0)
        self.grid_zoom_threshold_spin.setSuffix(" %")
        self.grid_zoom_threshold_spin.setValue(float(prefs.get("grid_disable_zoom_percent", 15.0)))
        self.grid_zoom_threshold_spin.setEnabled(self.optimize_grid_checkbox.isChecked())
        perf_form.addRow("Disable grid when zoom-out reaches:", self.grid_zoom_threshold_spin)

        layout.addLayout(perf_form)

        apply_label = QLabel("Apply Font to All Components")
        apply_label.setStyleSheet("font-weight:600; margin-top:8px;")
        layout.addWidget(apply_label)
        apply_hint = QLabel(
            "Changes the font used by every component on the current "
            "board and every other linked board in this project."
        )
        apply_hint.setWordWrap(True)
        apply_hint.setStyleSheet("color:#888; font-size:11px;")
        layout.addWidget(apply_hint)

        apply_row = QHBoxLayout()
        self.apply_font_combo = QFontComboBox()
        self.apply_font_combo.setCurrentFont(QFont(prefs.get("default_font_family", "Segoe UI")))
        apply_row.addWidget(self.apply_font_combo, 1)
        set_btn = QPushButton("Set")
        set_btn.clicked.connect(self._on_set_font_clicked)
        apply_row.addWidget(set_btn)
        layout.addLayout(apply_row)

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self._on_accept)
        buttons.rejected.connect(self.reject)
        layout.addWidget(buttons)

    def _on_optimize_grid_toggled(self, checked):
        self.grid_zoom_threshold_spin.setEnabled(checked)

    def _on_set_font_clicked(self):
        family = self.apply_font_combo.currentFont().family()
        count = self.main_window.apply_font_to_all_boards(family)
        QMessageBox.information(
            self, "Font Applied",
            f"Set font to \u201c{family}\u201d on {count} board file(s)."
        )

    def _on_accept(self):
        self.main_window.prefs["default_show_title"] = self.title_checkbox.isChecked()
        self.main_window.prefs["default_show_description"] = self.desc_checkbox.isChecked()
        self.main_window.prefs["default_title_alignment"] = self.align_combo.currentData()
        self.main_window.prefs["default_font_family"] = self.font_combo.currentFont().family()
        self.main_window.prefs["default_title_font_size"] = self.title_size_spin.value()
        self.main_window.prefs["default_description_font_size"] = self.desc_size_spin.value()
        self.main_window.prefs["default_arrow_size"] = self.arrow_size_spin.value()
        self.main_window.prefs["optimize_grid_rendering"] = self.optimize_grid_checkbox.isChecked()
        self.main_window.prefs["grid_disable_zoom_percent"] = self.grid_zoom_threshold_spin.value()
        checked_id = self.arrow_snap_group.checkedId()
        if 0 <= checked_id < len(ARROW_SNAP_METHOD_OPTIONS):
            self.main_window.prefs["default_arrow_snap_method"] = ARROW_SNAP_METHOD_OPTIONS[checked_id][0]
        save_app_preferences(self.main_window.prefs)
        self.main_window.scene.update()
        self.accept()


class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self._title_base = "OpenNote \u2014 Milanote-style Mind Map"
        self.setWindowTitle(self._title_base)
        self.resize(1440, 900)

        # -- app preferences (Settings > Preferences) ----------------------
        # Persisted across runs via QSettings and consulted whenever a new
        # component is created (see _new_component_font_defaults /
        # _apply_new_component_prefs below) - NOT retroactive to existing
        # components already on a board (that's what the separate
        # "apply font to all components" action in PreferencesDialog is
        # for, which walks every item on disk instead of just defaults
        # used at creation time).
        self.prefs = load_app_preferences()

        self.scene = MindMapScene(self)
        self.scene.main_window = self
        self.view = MindMapView(self.scene, self, self)

        # -- breadcrumb bar (nested-boards navigation) -----------------
        # Shows the current board's full logical path, e.g.
        # "Game > Weapons > Firearms", mirroring the path embedded in the
        # board's own HTML (see save/open below). Every segment but the
        # last is a clickable button that jumps straight to that ancestor
        # board file - the other way to navigate besides double-clicking
        # a BoardLinkItem shortcut card on the canvas itself.
        central = QWidget()
        central_layout = QVBoxLayout(central)
        central_layout.setContentsMargins(0, 0, 0, 0)
        central_layout.setSpacing(0)
        self.breadcrumb_bar = QWidget()
        self.breadcrumb_bar.setStyleSheet("background:#1b1b1b; border-bottom:1px solid #000;")
        self.breadcrumb_layout = QHBoxLayout(self.breadcrumb_bar)
        self.breadcrumb_layout.setContentsMargins(10, 4, 10, 4)
        self.breadcrumb_layout.setSpacing(2)
        self.breadcrumb_layout.addStretch(1)
        central_layout.addWidget(self.breadcrumb_bar)
        central_layout.addWidget(self.view)
        self.setCentralWidget(central)

        # Let dropping an .html board file anywhere on the window open it,
        # the same as File > Open... (see dragEnterEvent/dropEvent below).
        self.setAcceptDrops(True)

        self.clipboard_data = []
        self.current_file = None
        # The folder holding the current project's board .html files (every
        # board in a project lives flat inside one shared folder - see
        # BoardLinkItem and _ensure_project_and_file). Kept in sync with
        # os.path.dirname(self.current_file) whenever a board is
        # saved/opened, but tracked separately so it survives being asked
        # for explicitly (see choose_or_create_project_folder/new_project)
        # even before the very first save.
        self.project_dir = None
        # Full logical path (list of {"name","file"} dicts, self inclusive)
        # of whatever board is currently open - see _update_breadcrumb_bar,
        # navigate_to_file, and _write_html.
        self.breadcrumb = [{"name": "Untitled", "file": None}]
        self._editing_selection = None  # drawing/arrow items currently selected for restyling
        self._text_selection = None     # text-note/plain-text items currently selected for restyling
        self._font_selection = None     # text-note/plain-text/table items, for Font/B/I/U/Size
        self._arrow_selection = None    # arrow items currently selected, for the Line style combo
        self._other_selection = None    # image/gif/video/board-card items selected, for restyling
        # Which arrow's label is the "active" text-edit target, for the
        # Font/B/I/U/Size panel. Deliberately stickier than a live
        # scene.focusItem() check: some toolbar widgets (the font combo,
        # in particular) legitimately need real keyboard focus to work,
        # which knocks the label out of Qt's/the scene's focus without
        # the user ever "clicking away" from the arrow - see
        # on_selection_changed for where this gets updated/cleared.
        self._active_label_arrow = None
        # Same idea as _active_label_arrow, but for a BoardCardItem's
        # in-place "text" subitem editor (_SubitemTextEdit) - see
        # BoardCardItem.font_targets and on_selection_changed.
        self._active_text_board_card = None
        # (card, subitem-dict) currently single-click "selected" inside
        # a Board Card - see on_selection_changed/pick_color/
        # delete_selection. None whenever nothing is.
        self._selected_board_subitem = None
        # Mirrors _top_strip_selection above, but for a single-click
        # "selected" Board Card subitem (a plain dict, not a live
        # TopStripMixin instance, so it can't just be folded into that
        # list) - see on_selection_changed/on_top_strip_toggled.
        self._top_strip_selected_subitem = None
        # The most recent text item that was genuinely in edit mode -
        # kept around (independent of _active_label_arrow's narrower
        # "is this arrow's label the font-panel target" bookkeeping) so
        # a toolbar widget that must grab real keyboard focus (the font
        # combo, to let you type/search) can hand focus back afterward -
        # see _restore_text_edit_focus.
        self._last_edited_text_item = None

        # -- undo / redo -----------------------------------------------
        # Coarse but reliable: rather than a QUndoCommand per interaction
        # (every move/resize/text-edit/table-edit/property-change site
        # would need its own hook), we lean on the serialize()/load()
        # round-trip the app already has for save/open. Every settled
        # change to the scene gets captured as one more full-board JSON
        # snapshot in _undo_stack; undo/redo just swaps to the
        # neighboring snapshot. See _commit_undo_checkpoint for how
        # "settled" is decided.
        self.MAX_UNDO_STEPS = 100
        self._undo_stack = []       # past snapshots (JSON strings), oldest first
        self._redo_stack = []       # snapshots undone away from, most recent last
        self._undo_baseline = None  # JSON snapshot of the current committed state
        self._undo_restoring = False  # True while undo()/redo() itself is loading a snapshot
        self._undo_commit_timer = QTimer(self)
        self._undo_commit_timer.setSingleShot(True)
        self._undo_commit_timer.setInterval(600)
        self._undo_commit_timer.timeout.connect(self._commit_undo_checkpoint)

        self._build_toolbar()
        self.scene.selectionChanged.connect(self.on_selection_changed)
        # Entering/leaving in-place text edit mode doesn't change the
        # scene's *selection*, only its focus item - but the Color button
        # needs to know about it too (it targets text color while editing,
        # component color otherwise), so refresh on focus changes as well.
        self.scene.focusItemChanged.connect(self.on_selection_changed)
        # scene.changed fires for every visual change (move/resize/type/
        # draw/delete/property edits alike) - debounced via the timer
        # above so a whole drag or typing burst becomes one undo step
        # instead of one per pixel/keystroke. selectionChanged/
        # focusItemChanged additionally flush right away when there IS a
        # pending change, so e.g. finishing a text edit by clicking
        # another item doesn't wait out the full debounce.
        self.scene.changed.connect(self._on_scene_changed_for_undo)
        self.scene.selectionChanged.connect(self._flush_pending_undo_checkpoint)
        self.scene.focusItemChanged.connect(self._flush_pending_undo_checkpoint)
        self._build_menu()
        self.statusBar().showMessage(
            "Ready \u2014 Middle-mouse drag to pan \u00b7 Ctrl+Wheel to zoom \u00b7 Ctrl+D duplicate \u00b7 Drag a card onto a Board to nest it"
        )
        # -- status bar: zoom % (bottom-right, permanent) and board-load
        # progress (bottom-left, normal widget so it sits to the left of/
        # underneath any showMessage() text) - see _update_zoom_label /
        # _set_loading_progress_label / _on_board_load_progress.
        self.loading_label = QLabel()
        self.statusBar().addWidget(self.loading_label)
        self.zoom_label = QLabel()
        self.statusBar().addPermanentWidget(self.zoom_label)
        self._loading_progress_shown_pct = -1
        self._loading_progress_last_paint = 0.0
        self._update_zoom_label()
        self._update_breadcrumb_bar()
        # -- unsaved-changes tracking -------------------------------------
        # A snapshot of the last saved (or freshly loaded/started) state,
        # compared against the live scene on demand (_has_unsaved_changes)
        # instead of trying to flag "dirty" from every individual edit
        # site (move/resize/type/delete/...) - see _current_snapshot,
        # _confirm_discard_changes, and closeEvent below.
        self._saved_snapshot = None
        self._update_saved_snapshot()
        # Polls once a second rather than hooking every single mutation
        # site (move/resize/type/delete/...) - cheap enough for this
        # app's scale, and keeps the "*" prefix in sync without having to
        # thread a dirty-flag update through every edit path.
        self._title_timer = QTimer(self)
        self._title_timer.timeout.connect(self._refresh_title_bar)
        self._title_timer.start(1000)
        self._reset_undo_history()
    def _set_base_title(self, title):
        self._title_base = title
        self._refresh_title_bar()
    def _refresh_title_bar(self):
        base = getattr(self, "_title_base", "OpenNote")
        prefix = "*" if self._has_unsaved_changes() else ""
        self.setWindowTitle(prefix + base)
    # -- UI construction --------------------------------------------------

    # -- UI construction --------------------------------------------------
    def _build_menu(self):
        m = self.menuBar()
        file_menu = m.addMenu("&File")
        file_menu.addAction("New Board", self.new_board, QKeySequence.New)
        file_menu.addAction("New Project (Choose Folder)...", self.new_project)
        file_menu.addAction("Open...", self.open_board, QKeySequence.Open)
        self.recent_menu = file_menu.addMenu("Recent")
        file_menu.aboutToShow.connect(self._rebuild_recent_menu)
        file_menu.addAction("Save", self.save_board, QKeySequence.Save)
        file_menu.addAction("Save As...", self.save_board_as, QKeySequence.SaveAs)
        file_menu.addSeparator()
        file_menu.addAction("Refactor (Rename) Main Board...", self.rename_main_board)
        file_menu.addSeparator()
        file_menu.addAction("Exit", self.close)

        edit_menu = m.addMenu("&Edit")
        self.undo_action = edit_menu.addAction("Undo", self.undo, QKeySequence("Ctrl+Z"))
        self.redo_action = edit_menu.addAction("Redo", self.redo)
        self.redo_action.setShortcuts([QKeySequence("Ctrl+Y"), QKeySequence("Ctrl+Shift+Z")])
        self.undo_action.setEnabled(False)
        self.redo_action.setEnabled(False)
        edit_menu.addSeparator()
        edit_menu.addAction("Copy", self.copy_selection, QKeySequence.Copy)
        edit_menu.addAction("Paste", self.paste_clipboard, QKeySequence.Paste)
        edit_menu.addAction("Duplicate", self.duplicate_selection, QKeySequence("Ctrl+D"))
        edit_menu.addAction("Delete", self.delete_selection, QKeySequence.Delete)

        settings_menu = m.addMenu("&Settings")
        settings_menu.addAction("Preferences...", self.open_preferences)

    def _build_toolbar(self):
        tb = QToolBar("Tools")
        tb.setIconSize(QSize(20, 20))
        tb.setMovable(False)
        tb.setOrientation(Qt.Vertical)
        tb.setToolButtonStyle(Qt.ToolButtonTextBesideIcon)
        tb.setStyleSheet("""
            QToolBar { background:#1b1b1b; border:none; spacing:2px; padding:8px 4px; }
            QToolButton { color:#e8e8e8; padding:8px 10px; border-radius:6px; font-size:12px; }
            QToolButton:hover { background:#2a2a2a; }
            QToolButton:checked { background:#33465e; color:#8ab4ff; }
            QToolBar::separator { background:#333333; height:1px; margin:6px 10px; }
        """)
        self.addToolBar(Qt.LeftToolBarArea, tb)

        def add_action(text, slot, checkable=False, icon_kind=None):
            act = QAction(text, self)
            if icon_kind:
                act.setIcon(_make_toolbar_icon(icon_kind))
            act.setCheckable(checkable)
            if checkable:
                act.toggled.connect(slot)
            else:
                act.triggered.connect(slot)
            tb.addAction(act)
            return act

        add_action("Text Note", self.add_text_note, icon_kind="text")
        add_action("Text", self.add_text, icon_kind="plaintext")
        add_action("Board Card", self.add_board_card, icon_kind="board")
        add_action("Board Link", self.add_board_link, icon_kind="board_link")
        add_action("Table", self.add_table, icon_kind="table")
        tb.addSeparator()
        add_action("Add Image", self.add_image, icon_kind="image")
        add_action("Add GIF", self.add_gif, icon_kind="gif")
        add_action("Add Video", self.add_video, icon_kind="video")
        tb.addSeparator()
        self.draw_action = add_action("Draw", self.toggle_draw_mode, checkable=True, icon_kind="draw")

        arrow_btn = QToolButton()
        arrow_btn.setText("Arrow")
        arrow_btn.setIcon(_make_toolbar_icon("arrow"))
        arrow_btn.setIconSize(QSize(20, 20))
        arrow_btn.setToolButtonStyle(Qt.ToolButtonTextBesideIcon)
        arrow_btn.setPopupMode(QToolButton.InstantPopup)
        arrow_menu = QMenu(arrow_btn)
        for st in ArrowItem.STYLES:
            act = arrow_menu.addAction(ArrowItem.STYLE_LABELS[st])
            act.triggered.connect(lambda checked=False, s=st: self.add_arrow(s))
        arrow_btn.setMenu(arrow_menu)
        arrow_btn.clicked.connect(lambda: self.add_arrow("single"))
        tb.addWidget(arrow_btn)
        tb.addSeparator()
        add_action("Duplicate", self.duplicate_selection, icon_kind="duplicate")
        add_action("Delete", self.delete_selection, icon_kind="delete")
        tb.addSeparator()
        self.select_action = add_action(
            "Select", lambda checked: None, checkable=True, icon_kind="select"
        )

        # Draw / Select behave like a two-state tool switch: picking one
        # always unchecks the other. toggle_draw_mode (connected above via
        # `toggled`) fires either way, so it's the single source of truth
        # for switching the canvas between click-to-select/rubber-band
        # mode and freehand-draw mode.
        self.tool_group = QActionGroup(self)
        self.tool_group.setExclusive(True)
        self.tool_group.addAction(self.draw_action)
        self.tool_group.addAction(self.select_action)
        self.select_action.setChecked(True)

        draw_tb = QToolBar("Drawing Options")
        self.addToolBar(Qt.TopToolBarArea, draw_tb)

        self.brush_label_action = draw_tb.addWidget(QLabel(" Brush: "))
        self.brush_combo = QComboBox()
        self.brush_combo.addItems(["Pen", "Marker", "Highlighter"])
        self.brush_combo.currentTextChanged.connect(self.on_brush_type_changed)
        self.brush_combo_action = draw_tb.addWidget(self.brush_combo)
        # Only meaningful while actively drawing - hidden the rest of the
        # time (see toggle_draw_mode) so it doesn't clutter the toolbar
        # when e.g. Select is the active tool.
        self.brush_label_action.setVisible(False)
        self.brush_combo_action.setVisible(False)

        draw_tb.addWidget(QLabel("  Color: "))
        self.color_btn = QPushButton()
        self.color_btn.setFixedSize(26, 26)
        # NoFocus is essential here: this button is also used to recolor
        # the TEXT of a note while it's being edited (see pick_color /
        # _focused_text_item, which target whatever QGraphicsTextItem
        # currently has focus). QPushButton grabs keyboard focus on
        # click by default, which would steal focus away from the text
        # item *before* the clicked() signal even fires - at that point
        # _focused_text_item() finds nothing focused and pick_color()
        # falls back to recoloring the whole note instead of its text.
        # Keeping this button out of the focus chain lets the text item
        # stay focused (and its selection intact) while the color picker
        # is used.
        self.color_btn.setFocusPolicy(Qt.NoFocus)
        self._set_brush_color(QColor("#ffffff"))
        self.color_btn.clicked.connect(self.pick_color)
        draw_tb.addWidget(self.color_btn)

        # -- Size group (label + slider + spinbox) -----------------------
        # All three live in one small container with a fixed 8px gap
        # between them, instead of being added to the toolbar as three
        # separate widgets - the toolbar's own layout hands leftover
        # horizontal space to whichever of its widgets can take it
        # (sliders included), which was stretching them kilometers apart.
        size_group = QWidget()
        size_group.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)
        size_group_layout = QHBoxLayout(size_group)
        size_group_layout.setContentsMargins(0, 0, 0, 0)
        size_group_layout.setSpacing(8)
        size_group_layout.addWidget(QLabel("  Size: "))

        self.size_slider = QSlider(Qt.Horizontal)
        self.size_slider.setRange(1, 40)
        self.size_slider.setValue(4)
        self.size_slider.setFixedWidth(140)
        # QSlider defaults to an Expanding horizontal size policy - even
        # capped at 140px above, that flag alone was enough for the
        # surrounding layout to hand this group extra space it couldn't
        # actually use, showing up as a gap. Pin it down explicitly.
        self.size_slider.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)
        # Same reasoning as color_btn's NoFocus above: a QSlider grabs
        # keyboard focus by default, which would end whatever text item
        # is currently being edited (its focusOutEvent drops edit mode)
        # the instant the slider is touched - most visibly breaking an
        # Arrow's label, whose font controls only show up while it's
        # actively focused/being edited.
        self.size_slider.setFocusPolicy(Qt.NoFocus)
        self.size_slider.valueChanged.connect(self.on_size_changed)
        size_group_layout.addWidget(self.size_slider)

        self.size_stepper = NumberStepper(1, 40)
        self.size_stepper.setValue(4)
        self.size_slider.valueChanged.connect(self.size_stepper.setValue)
        self.size_stepper.valueChanged.connect(self.size_slider.setValue)
        size_group_layout.addWidget(self.size_stepper)
        draw_tb.addWidget(size_group)

        # -- Opacity group (label + slider + spinbox) --------------------
        opacity_group = QWidget()
        opacity_group.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)
        opacity_group_layout = QHBoxLayout(opacity_group)
        opacity_group_layout.setContentsMargins(0, 0, 0, 0)
        opacity_group_layout.setSpacing(8)
        opacity_group_layout.addWidget(QLabel("  Opacity: "))

        self.opacity_slider = QSlider(Qt.Horizontal)
        self.opacity_slider.setRange(5, 100)
        self.opacity_slider.setValue(100)
        self.opacity_slider.setFixedWidth(120)
        self.opacity_slider.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Fixed)
        self.opacity_slider.setFocusPolicy(Qt.NoFocus)
        self.opacity_slider.valueChanged.connect(self.on_opacity_changed)
        opacity_group_layout.addWidget(self.opacity_slider)

        self.opacity_stepper = NumberStepper(5, 100)
        self.opacity_stepper.setValue(100)
        self.opacity_slider.valueChanged.connect(self.opacity_stepper.setValue)
        self.opacity_stepper.valueChanged.connect(self.opacity_slider.setValue)
        opacity_group_layout.addWidget(self.opacity_stepper)
        draw_tb.addWidget(opacity_group)


        # -- arrow style control (Arrow only) -----------------------------
        # Same idea as Line style below, but for the arrowhead kind
        # itself (single/double head, or a plain line with no head) -
        # previously only reachable via the right-click "Arrow Style"
        # submenu.
        self.arrow_style_label_action = draw_tb.addWidget(QLabel("  Arrow: "))
        self.arrow_style_combo = QComboBox()
        for st in ArrowItem.STYLES:
            self.arrow_style_combo.addItem(ArrowItem.STYLE_LABELS[st], st)
        self.arrow_style_combo.currentIndexChanged.connect(self.on_arrow_style_changed)
        self.arrow_style_action = draw_tb.addWidget(self.arrow_style_combo)
        self.arrow_style_label_action.setVisible(False)
        self.arrow_style_action.setVisible(False)

        # -- line style control (Arrow only) -----------------------------
        # Hidden by default; on_selection_changed shows it only while at
        # least one arrow is selected, so choosing solid/dashed/dash-dot
        # is available right in the top panel instead of only the
        # right-click menu.
        self.line_style_label = QLabel("  Line: ")
        self.line_style_label_action = draw_tb.addWidget(self.line_style_label)
        self.line_style_combo = QComboBox()
        for ls in ArrowItem.LINE_STYLES:
            self.line_style_combo.addItem(ArrowItem.LINE_STYLE_LABELS[ls], ls)
        self.line_style_combo.currentIndexChanged.connect(self.on_line_style_changed)
        self.line_style_action = draw_tb.addWidget(self.line_style_combo)
        self.line_style_label_action.setVisible(False)
        self.line_style_action.setVisible(False)

        # -- per-component checkboxes (Title / Show label / Show Title /
        # Show Description) - each hidden by default; on_selection_changed
        # shows the relevant one(s) depending on what's selected. A
        # leading separator plus extra left/right padding (via the
        # checkbox stylesheet) keeps this little group from crowding up
        # against the slider/combo controls on either side of it.
        checkbox_style = "QCheckBox { padding-left: 6px; padding-right: 10px; }"

        self.checkbox_group_sep = draw_tb.addSeparator()

        # Off by default (see DrawingItem.allow_board_card) - dragging a
        # sketch onto a Board Card would otherwise silently flatten it
        # into a plain image subitem, which isn't always wanted. Shown
        # only while a Drawing is selected (see on_selection_changed).
        self.allow_board_card_checkbox = QCheckBox("  Allow to be Board Card element")
        self.allow_board_card_checkbox.setStyleSheet(checkbox_style)
        self.allow_board_card_checkbox.setFocusPolicy(Qt.NoFocus)
        self.allow_board_card_checkbox_action = draw_tb.addWidget(self.allow_board_card_checkbox)
        self.allow_board_card_checkbox.toggled.connect(self.on_allow_board_card_toggled)
        self.allow_board_card_checkbox_action.setVisible(False)

        self.title_checkbox = QCheckBox("  Title")
        self.title_checkbox.setStyleSheet(checkbox_style)
        self.title_checkbox.setFocusPolicy(Qt.NoFocus)
        self.title_checkbox_action = draw_tb.addWidget(self.title_checkbox)
        self.title_checkbox.toggled.connect(self.on_title_toggled)
        self.title_checkbox_action.setVisible(False)

        self.arrow_label_checkbox = QCheckBox("  Show label")
        self.arrow_label_checkbox.setStyleSheet(checkbox_style)
        self.arrow_label_checkbox.setFocusPolicy(Qt.NoFocus)
        self.arrow_label_checkbox_action = draw_tb.addWidget(self.arrow_label_checkbox)
        self.arrow_label_checkbox.toggled.connect(self.on_arrow_label_toggled)
        self.arrow_label_checkbox_action.setVisible(False)

        self.media_title_checkbox = QCheckBox("  Show Title")
        self.media_title_checkbox.setStyleSheet(checkbox_style)
        self.media_title_checkbox.setFocusPolicy(Qt.NoFocus)
        self.media_title_checkbox_action = draw_tb.addWidget(self.media_title_checkbox)
        self.media_title_checkbox.toggled.connect(self.on_media_title_toggled)
        self.media_title_checkbox_action.setVisible(False)

        self.media_desc_checkbox = QCheckBox("  Show Description")
        self.media_desc_checkbox.setStyleSheet(checkbox_style)
        self.media_desc_checkbox.setFocusPolicy(Qt.NoFocus)
        self.media_desc_checkbox_action = draw_tb.addWidget(self.media_desc_checkbox)
        self.media_desc_checkbox.toggled.connect(self.on_media_desc_toggled)
        self.media_desc_checkbox_action.setVisible(False)

        # Board Link's own toggleable description field - same toggle
        # idea as Text Note's "Title" checkbox above, just for Board
        # Link cards (see BoardLinkItem.show_description).
        self.board_link_desc_checkbox = QCheckBox("  Description")
        self.board_link_desc_checkbox.setStyleSheet(checkbox_style)
        self.board_link_desc_checkbox.setFocusPolicy(Qt.NoFocus)
        self.board_link_desc_checkbox_action = draw_tb.addWidget(self.board_link_desc_checkbox)
        self.board_link_desc_checkbox.toggled.connect(self.on_board_link_desc_toggled)
        self.board_link_desc_checkbox_action.setVisible(False)

        # Top Strip - available on Text Note, Image, GIF, Video and Board
        # Card (see TopStripMixin) - so this one checkbox covers several
        # otherwise-unrelated component types at once, unlike the
        # type-specific checkboxes above.
        self.top_strip_checkbox = QCheckBox("  Top Strip")
        self.top_strip_checkbox.setStyleSheet(checkbox_style)
        self.top_strip_checkbox.setFocusPolicy(Qt.NoFocus)
        self.top_strip_checkbox_action = draw_tb.addWidget(self.top_strip_checkbox)
        self.top_strip_checkbox.toggled.connect(self.on_top_strip_toggled)
        self.top_strip_checkbox_action.setVisible(False)

        # -- text formatting controls (Text Note / Text only) -----------
        # Hidden by default; on_selection_changed shows them only while a
        # text component is selected, so they don't clutter the toolbar
        # the rest of the time. Color/Size/Opacity above double up for
        # text too (text color, font size, item opacity) the same way
        # they already double up for drawings/arrows.
        self.text_format_sep = draw_tb.addSeparator()

        self.font_label_action = draw_tb.addWidget(QLabel("  Font: "))
        self.font_combo = _FontFamilyCombo(self._restore_text_edit_focus)
        self.font_combo.setEditable(True)
        self.font_combo.setInsertPolicy(QComboBox.NoInsert)
        self.font_combo.setFixedWidth(180)
        self.font_combo.lineEdit().setPlaceholderText("Search font\u2026")
        # Why Size/Opacity/B/I/U never interrupt the label being edited
        # but this combo did: those all sit on Qt.NoFocus, so clicking
        # them never moves keyboard focus away from the canvas in the
        # first place - there's nothing for the text item's focusOutEvent
        # to react to. This combo genuinely needs focus for one thing
        # only: typing into its search field. Clicking the dropdown arrow
        # to pick a font with the mouse - the common case - doesn't need
        # focus at all. So: NoFocus on the combo itself (arrow clicks stay
        # mouse-only, exactly like the other controls), while the
        # embedded line edit below keeps its own normal focus policy, so
        # clicking directly into the text field to type a search still
        # works (and still is the one case where focus - and the
        # transient interruption that comes with it - is expected).
        self.font_combo.setFocusPolicy(Qt.NoFocus)
        self.font_combo.lineEdit().setFocusPolicy(Qt.StrongFocus)
        # Give it a completer that matches anywhere in the name (not just
        # the start), case-insensitively, so e.g. typing "mono" surfaces
        # "DejaVu Sans Mono" too.
        font_completer = self.font_combo.completer()
        font_completer.setCompletionMode(QCompleter.PopupCompletion)
        font_completer.setFilterMode(Qt.MatchContains)
        font_completer.setCaseSensitivity(Qt.CaseInsensitive)
        self.font_combo.setCompleter(font_completer)
        self.font_combo.currentFontChanged.connect(self.on_font_family_changed)
        self.font_action = draw_tb.addWidget(self.font_combo)
        # Let every EditableTextItem recognize this specific combo (see
        # EditableTextItem._losing_focus_to_font_combo) so on the rare
        # occasions this combo *does* end up taking real focus (typing to
        # search), losing focus to it doesn't visibly knock the text
        # being edited out of edit mode. Restoring focus itself (on
        # selection *and* on the dropdown simply closing, e.g. Escape or
        # re-picking the same font) is handled by _FontFamilyCombo's
        # hidePopup override and on_font_family_changed.
        EditableTextItem._font_combo = self.font_combo
        EditableTextItem._toolbar_refresh_cb = self._refresh_text_format_buttons

        self.bold_btn = QToolButton()
        self.bold_btn.setText("B")
        self.bold_btn.setCheckable(True)
        self.bold_btn.setToolTip("Bold")
        self.bold_btn.setStyleSheet("font-weight:bold;")
        self.bold_btn.setFocusPolicy(Qt.NoFocus)
        self.bold_btn.toggled.connect(self.on_bold_toggled)
        self.bold_action = draw_tb.addWidget(self.bold_btn)

        self.italic_btn = QToolButton()
        self.italic_btn.setText("I")
        self.italic_btn.setCheckable(True)
        self.italic_btn.setToolTip("Italic")
        self.italic_btn.setStyleSheet("font-style:italic;")
        self.italic_btn.setFocusPolicy(Qt.NoFocus)
        self.italic_btn.toggled.connect(self.on_italic_toggled)
        self.italic_action = draw_tb.addWidget(self.italic_btn)

        self.underline_btn = QToolButton()
        self.underline_btn.setText("U")
        self.underline_btn.setCheckable(True)
        self.underline_btn.setToolTip("Underline")
        self.underline_btn.setStyleSheet("text-decoration:underline;")
        self.underline_btn.setFocusPolicy(Qt.NoFocus)
        self.underline_btn.toggled.connect(self.on_underline_toggled)
        self.underline_action = draw_tb.addWidget(self.underline_btn)

        # -- text alignment (Left / Center / Right) ----------------------
        # One dropdown button rather than three separate toggles, since
        # the three options are mutually exclusive (a paragraph has
        # exactly one alignment, never a combination) - a QActionGroup
        # inside the popup menu enforces that. Shown/hidden together with
        # Font/B/I/U (see _font_format_actions) and kept in sync with the
        # live cursor the same way (see _refresh_text_format_buttons /
        # on_selection_changed).
        self.align_btn = QToolButton()
        self.align_btn.setToolTip("Text alignment")
        self.align_btn.setPopupMode(QToolButton.InstantPopup)
        self.align_btn.setFocusPolicy(Qt.NoFocus)
        align_menu = QMenu(self.align_btn)
        self.align_group = QActionGroup(self)
        self.align_group.setExclusive(True)
        self._align_actions = {}
        for label, alignment in (("Left", Qt.AlignLeft), ("Center", Qt.AlignHCenter), ("Right", Qt.AlignRight)):
            act = QAction(label, self)
            act.setCheckable(True)
            act.triggered.connect(lambda checked, a=alignment: self.on_align_changed(a))
            align_menu.addAction(act)
            self.align_group.addAction(act)
            self._align_actions[alignment] = act
        self.align_btn.setMenu(align_menu)
        self._set_align_button(Qt.AlignLeft)
        # aboutToShow fires synchronously, right before the popup steals
        # focus - the live text cursor is still exactly where the user
        # left it at that point, so this is what guarantees the menu
        # always opens showing the field's *actual* current alignment,
        # regardless of whether some earlier click happened to skip a
        # _refresh_text_format_buttons()/on_selection_changed() call
        # (only mouseReleaseEvent/keyReleaseEvent trigger those - not
        # every possible way a click can land the cursor somewhere new).
        align_menu.aboutToShow.connect(self._refresh_align_button_now)
        self.align_action = draw_tb.addWidget(self.align_btn)

        self.link_btn = QToolButton()
        self.link_btn.setText("Link")
        self.link_btn.setToolTip("Add / edit hyperlink")
        self.link_btn.setCheckable(True)
        self.link_btn.setFocusPolicy(Qt.NoFocus)
        self.link_btn.clicked.connect(self.on_hyperlink_clicked)
        self.link_action = draw_tb.addWidget(self.link_btn)

        # -- text highlight (background color behind a run of text) -----
        # A plain checkable toggle, mirroring Bold/Italic/Underline above -
        # shows pressed/active exactly when the current cursor position/
        # selection already has a highlight (see _refresh_text_format_
        # buttons). There used to be a second color-swatch button next to
        # this one just for picking the highlight color; that's gone now -
        # while a highlight is active, the main Color button/window (see
        # MainWindow.pick_color) grows a "Highlight" tab instead, the same
        # way it grows a "Top Strip" tab for components that have one.
        self.highlight_btn = QToolButton()
        self.highlight_btn.setText("Highlight")
        self.highlight_btn.setToolTip("Text highlight")
        self.highlight_btn.setCheckable(True)
        self.highlight_btn.setFocusPolicy(Qt.NoFocus)
        self.highlight_btn.toggled.connect(self.on_highlight_toggled)
        self.highlight_action = draw_tb.addWidget(self.highlight_btn)

        self.highlight_color = QColor("#ffff00")

        # Placed last on the toolbar (rather than beside Brush, where it
        # used to live) so it always sits at the far end of the bar.
        self.eraser_checkbox = QCheckBox("  Eraser")
        self.eraser_checkbox.setFocusPolicy(Qt.NoFocus)
        self.eraser_checkbox.setStyleSheet("margin-left: 8px;")
        self.eraser_checkbox.toggled.connect(self.on_eraser_toggled)
        self.eraser_checkbox_action = draw_tb.addWidget(self.eraser_checkbox)
        # Only meaningful while actively drawing - hidden the rest of the
        # time (see toggle_draw_mode), same as the Brush combo above.
        self.eraser_checkbox_action.setVisible(False)

        self._font_format_actions = [
            self.text_format_sep, self.font_label_action, self.font_action,
            self.bold_action, self.italic_action, self.underline_action,
            self.align_action, self.highlight_action,
        ]
        self._text_format_actions = self._font_format_actions + [self.link_action]
        for a in self._text_format_actions:
            a.setVisible(False)

    # -- brush controls -----------------------------------------------
    # These same controls (Color button, Size slider, Opacity slider) do
    # double duty: with nothing suitable selected they set the pen used
    # for the *next* stroke/arrow; with a drawing or arrow selected they
    # instead restyle the selected object(s) live, so the user can just
    # select something and drag the sliders / pick a color to change it.
    def _set_brush_color(self, color):
        self.color_btn.setStyleSheet(f"background-color:{color.name()}; border:1px solid #888;")
        self.scene.brush_color = color

    def _focused_text_item(self):
        """Return the QGraphicsTextItem currently in in-place edit mode
        (double-clicked into), if any. While one is active, the Color
        button targets that text's own color instead of the color of the
        component as a whole - this is also what "text selected" means
        here, since selecting a range of text only happens while editing."""
        fi = self.scene.focusItem()
        if (
            fi is not None
            and hasattr(fi, "textInteractionFlags")
            and fi.textInteractionFlags() == Qt.TextEditorInteraction
        ):
            return fi
        return None

    def on_selection_changed(self):
        if self.scene.rubber_band_dragging:
            # Skipped mid-drag for performance - this does dozens of
            # toolbar-widget updates, and Qt emits selectionChanged on
            # nearly every mouseMoveEvent of a rubber-band drag. See
            # MindMapScene.rubber_band_dragging / MindMapView for where
            # this gets called once for real right after the drag ends.
            return
        all_sel = self.scene.selectedItems()
        sel = [it for it in all_sel if isinstance(it, (DrawingItem, ArrowItem))]
        text_sel = [it for it in all_sel if isinstance(it, (TextNoteItem, PlainTextItem))]
        table_sel = [it for it in all_sel if isinstance(it, TableItem)]
        # Image/GIF/Video components each carry a title + description
        # text pair (see MediaCardMixin.font_targets) that should get the
        # exact same Font/B/I/U/Size toolbar treatment as a Text Note.
        media_sel = [it for it in all_sel if isinstance(it, MediaCardMixin)]
        text_note_sel = [it for it in all_sel if isinstance(it, TextNoteItem)]
        editing_item = self._focused_text_item()
        if editing_item is None and self._last_edited_text_item is not None:
            # scene.focusItem() can report None even while a text item is
            # still genuinely mid-edit: opening a popup (e.g. the Align
            # dropdown's QMenu, or the font-family combo) steals real Qt
            # widget focus from the QGraphicsView, which is enough to
            # make the scene report no focus item - even though
            # focusOutEvent (see EditableTextItem) deliberately left the
            # item's own TextEditorInteraction flag untouched for exactly
            # this case. Without this check, that momentary None was
            # trusted at face value here, wiping _last_edited_text_item /
            # _active_text_board_card and making every "current field"
            # font_targets() call below return [] - which is what made
            # the toolbar flash to generic defaults (Segoe UI 10, Align:
            # Left, white) instead of the field's real live formatting
            # the instant a dropdown was opened.
            try:
                still_editing = (
                    self._last_edited_text_item.textInteractionFlags() == Qt.TextEditorInteraction
                )
            except RuntimeError:
                still_editing = False
            if still_editing:
                editing_item = self._last_edited_text_item
        if editing_item is not None:
            self._last_edited_text_item = editing_item
        elif self._last_edited_text_item is not None:
            try:
                parent = self._last_edited_text_item.parentItem()
                still_referenced = parent in all_sel
            except RuntimeError:
                # Obiekt C++ już usunięty - dzieje się tak, gdy
                # scene.load()/clear_board() kasuje starą planszę (np.
                # powrót do głównego boarda) w trakcie gdy to wciąż był
                # "sticky" ostatnio edytowany tekst, a selectionChanged/
                # focusItemChanged odpalają się w trakcie tego teardownu.
                still_referenced = False
            if not still_referenced:
                self._last_edited_text_item = None
        arrow_sel = [it for it in all_sel if isinstance(it, ArrowItem)]
        # An arrow's label joins the font-toolbar selection while its text
        # is being edited - otherwise the Size slider means stroke width,
        # not font size (see the `elif sel:` branch below). This is kept
        # "sticky" via _active_label_arrow rather than re-checking live
        # focus every time: the font-family combo legitimately needs real
        # keyboard focus to work, which would otherwise knock the label
        # out of edit mode (and this whole panel out of view) the instant
        # it's clicked, well before the user is done with it. It only
        # actually clears once the arrow itself is no longer selected.
        if editing_item is not None and isinstance(editing_item.parentItem(), ArrowItem):
            self._active_label_arrow = editing_item.parentItem()
        elif self._active_label_arrow not in arrow_sel:
            self._active_label_arrow = None
        arrow_label_sel = [it for it in arrow_sel if it is self._active_label_arrow]
        # Same "sticky" idea as arrow_label_sel above, but for a
        # BoardCardItem's title or its in-place "text" subitem editor -
        # without this, neither ever gets the Font/B/I/U/Size controls
        # the way every other text-bearing component does, since a
        # BoardCardItem's subitem text lives in self.subitems rather
        # than a permanent QGraphicsTextItem child (see
        # BoardCardItem.font_targets and _SubitemTextEdit).
        #
        # Unlike arrow_label_sel, this deliberately does NOT check
        # scene.selectedItems(): BoardCardItem.mousePressEvent skips
        # calling super() (and so skips Qt's default click-to-select)
        # whenever the press lands on a subitem, precisely so dragging
        # to reorder/detach a subitem doesn't also select the whole
        # card - which means a card being edited via double-click on a
        # subitem is essentially never actually "selected". Clearing is
        # instead driven directly by whether that specific edit is
        # still live.
        # A Board Card subitem that's single-click "selected" (not being
        # edited) - see BoardCardItem._selected_sub_index/_select_subitem
        # and MindMapScene.select_board_subitem. Computed once here and
        # reused below (font_sel inclusion, color swatch, pick_color,
        # delete_selection) so a subitem gets the same top-toolbar
        # editing a standalone component gets when simply selected.
        selected_sub_card = self.scene._subitem_selected_card
        selected_sub = None
        if selected_sub_card is not None:
            try:
                si = selected_sub_card._selected_sub_index
                if si is not None and si < len(selected_sub_card.subitems):
                    selected_sub = selected_sub_card.subitems[si]
            except RuntimeError:
                selected_sub_card = None
        selected_sub_is_text = selected_sub is not None and selected_sub.get("kind") == "text"
        self._selected_board_subitem = (
            (selected_sub_card, selected_sub) if selected_sub is not None else None
        )
        if editing_item is not None and isinstance(editing_item.parentItem(), BoardCardItem) and (
            editing_item is editing_item.parentItem().title_item
            or editing_item.parentItem()._sub_edit_item is editing_item
        ):
            self._active_text_board_card = editing_item.parentItem()
        elif editing_item is None and selected_sub_is_text:
            self._active_text_board_card = selected_sub_card
        elif self._active_text_board_card is not None:
            card = self._active_text_board_card
            try:
                still_active = (
                    card.title_item.textInteractionFlags() == Qt.TextEditorInteraction
                    or card._sub_edit_item is not None
                    or (card is selected_sub_card and selected_sub_is_text)
                )
            except RuntimeError:
                still_active = False
            if not still_active:
                self._active_text_board_card = None
        board_text_sel = [self._active_text_board_card] if self._active_text_board_card is not None else []
        # Board Link's own description field (see BoardLinkItem.font_targets)
        # should get the same Font/B/I/U/Size toolbar treatment as a Text
        # Note's body text while it's being edited.
        board_link_sel = [it for it in all_sel if isinstance(it, BoardLinkItem)]
        # Anything with a font to edit via the toolbar's Font/B/I/U/Size
        # controls - Text Note, plain Text, Table (whose cells each carry
        # their own font - see TableItem.font_targets), media items, an
        # arrow's label, a BoardCardItem's text subitem, and a Board
        # Link's description field, each while being edited.
        font_sel = text_sel + table_sel + media_sel + arrow_label_sel + board_text_sel + board_link_sel
        # Every other component type (Image/GIF/Video/BoardCard, ...) -
        # these only ever have a single "color" (border/fill), so the
        # Color button can restyle them directly whenever one is the
        # whole thing that's selected, the same as Drawing/Arrow already do.
        other_sel = [
            it for it in all_sel
            if isinstance(it, BaseComponentItem)
            and not isinstance(it, (DrawingItem, ArrowItem, TextNoteItem, PlainTextItem))
        ]
        self._editing_selection = sel or None
        self._text_selection = text_sel or None
        self._font_selection = font_sel or None
        self._arrow_selection = arrow_sel or None
        self._other_selection = other_sel or None

        for a in self._font_format_actions:
            a.setVisible(bool(font_sel))
        # The Link button stays Text-Note/plain-Text only - a table cell
        # has no per-cell hyperlink concept.
        self.link_action.setVisible(bool(text_sel))

        self.line_style_label_action.setVisible(bool(arrow_sel))
        self.line_style_action.setVisible(bool(arrow_sel))
        self.arrow_style_label_action.setVisible(bool(arrow_sel))
        self.arrow_style_action.setVisible(bool(arrow_sel))
        if arrow_sel:
            self.line_style_combo.blockSignals(True)
            idx = self.line_style_combo.findData(arrow_sel[0].line_style)
            self.line_style_combo.setCurrentIndex(max(0, idx))
            self.line_style_combo.blockSignals(False)
            self.arrow_style_combo.blockSignals(True)
            idx = self.arrow_style_combo.findData(arrow_sel[0].style)
            self.arrow_style_combo.setCurrentIndex(max(0, idx))
            self.arrow_style_combo.blockSignals(False)

        self._text_note_selection = text_note_sel or None
        # A single-click-selected Board Card "text" subitem that came
        # from a TextNoteItem (not a plain-text note - those have no
        # title bar at all) gets the exact same Title checkbox treatment
        # as its standalone counterpart, just stored as a plain dict -
        # mirrors the analogous _top_strip_selected_subitem handling
        # further below, which this file already does for Top Strip.
        selected_sub_is_text_note = (
            selected_sub is not None and selected_sub.get("kind") == "text"
            and selected_sub.get("note_type") != "plaintext"
        )
        self._title_selected_subitem = (
            (selected_sub_card, selected_sub) if selected_sub_is_text_note else None
        )
        self.title_checkbox_action.setVisible(bool(text_note_sel) or selected_sub_is_text_note)
        if text_note_sel:
            self.title_checkbox.blockSignals(True)
            self.title_checkbox.setChecked(text_note_sel[0].show_title)
            self.title_checkbox.blockSignals(False)
        elif selected_sub_is_text_note:
            self.title_checkbox.blockSignals(True)
            self.title_checkbox.setChecked(bool(selected_sub.get("show_title")))
            self.title_checkbox.blockSignals(False)

        drawing_sel = [it for it in all_sel if isinstance(it, DrawingItem)]
        self._drawing_selection = drawing_sel or None
        self.allow_board_card_checkbox_action.setVisible(bool(drawing_sel))
        if drawing_sel:
            self.allow_board_card_checkbox.blockSignals(True)
            self.allow_board_card_checkbox.setChecked(drawing_sel[0].allow_board_card)
            self.allow_board_card_checkbox.blockSignals(False)

        self.arrow_label_checkbox_action.setVisible(bool(arrow_sel))
        if arrow_sel:
            self.arrow_label_checkbox.blockSignals(True)
            self.arrow_label_checkbox.setChecked(arrow_sel[0].show_label)
            self.arrow_label_checkbox.blockSignals(False)

        self._media_selection = media_sel or None
        # Same idea as selected_sub_is_text_note above, but for an
        # image/gif/video Board Card subitem - these always carry
        # show_title/show_description regardless of where they came from.
        selected_sub_is_media = selected_sub is not None and selected_sub.get("kind") in ("image", "gif", "video")
        self._media_selected_subitem = (
            (selected_sub_card, selected_sub) if selected_sub_is_media else None
        )
        self.media_title_checkbox_action.setVisible(bool(media_sel) or selected_sub_is_media)
        self.media_desc_checkbox_action.setVisible(bool(media_sel) or selected_sub_is_media)
        if media_sel:
            self.media_title_checkbox.blockSignals(True)
            self.media_title_checkbox.setChecked(media_sel[0].show_title)
            self.media_title_checkbox.blockSignals(False)
            self.media_desc_checkbox.blockSignals(True)
            self.media_desc_checkbox.setChecked(media_sel[0].show_description)
            self.media_desc_checkbox.blockSignals(False)
        elif selected_sub_is_media:
            self.media_title_checkbox.blockSignals(True)
            self.media_title_checkbox.setChecked(bool(selected_sub.get("show_title", True)))
            self.media_title_checkbox.blockSignals(False)
            self.media_desc_checkbox.blockSignals(True)
            self.media_desc_checkbox.setChecked(bool(selected_sub.get("show_description", True)))
            self.media_desc_checkbox.blockSignals(False)

        # Top Strip - Text Note, Image, GIF, Video, Board Card (see
        # TopStripMixin) - a single checkbox spanning several otherwise
        # unrelated component types, mirrored by all_sel rather than any
        # one of the type-specific *_sel lists above.
        top_strip_sel = [it for it in all_sel if isinstance(it, TopStripMixin)]
        self._top_strip_selection = top_strip_sel or None
        # A single-click-selected Board Card subitem has the exact same
        # Top Strip role as its standalone counterpart, just stored as a
        # plain dict (kind "image"/"gif"/"video" always has it; kind
        # "text" only when it came from a TextNoteItem, not a plain-text
        # note - see component_to_subitem/subitem_to_component) - can't
        # be folded into top_strip_sel above since it isn't a live
        # TopStripMixin instance, so it's tracked separately here and in
        # on_top_strip_toggled.
        selected_sub_has_strip = selected_sub is not None and (
            selected_sub.get("kind") in ("image", "gif", "video")
            or (selected_sub.get("kind") == "text" and selected_sub.get("note_type") != "plaintext")
        )
        self._top_strip_selected_subitem = (
            (selected_sub_card, selected_sub) if selected_sub_has_strip else None
        )
        self.top_strip_checkbox_action.setVisible(bool(top_strip_sel) or selected_sub_has_strip)
        if top_strip_sel:
            self.top_strip_checkbox.blockSignals(True)
            self.top_strip_checkbox.setChecked(top_strip_sel[0].top_strip_enabled)
            self.top_strip_checkbox.blockSignals(False)
        elif selected_sub_has_strip:
            self.top_strip_checkbox.blockSignals(True)
            self.top_strip_checkbox.setChecked(bool(selected_sub.get("top_strip_enabled")))
            self.top_strip_checkbox.blockSignals(False)

        self._board_link_selection = board_link_sel or None
        self.board_link_desc_checkbox_action.setVisible(bool(board_link_sel))
        if board_link_sel:
            self.board_link_desc_checkbox.blockSignals(True)
            self.board_link_desc_checkbox.setChecked(board_link_sel[0].show_description)
            self.board_link_desc_checkbox.blockSignals(False)

        # Only show the leading separator (and its extra spacing) when at
        # least one of the checkboxes it introduces is actually visible -
        # otherwise it'd leave a stray divider mark on the toolbar even
        # with nothing selected.
        self.checkbox_group_sep.setVisible(
            bool(text_note_sel or arrow_sel or media_sel or top_strip_sel or board_link_sel or selected_sub_has_strip)
        )

        if editing_item is not None:
            # In-place text editing (or a text selection within it) takes
            # priority for the color swatch: it previews the TEXT color,
            # not whatever the component's own color happens to be.
            col = editing_item.defaultTextColor()
            self.color_btn.setStyleSheet(f"background-color:{col.name()}; border:1px solid #888;")

        if font_sel:
            first = font_sel[0]
            font = _representative_font(first, editing_item)
            if editing_item is None:
                # Not editing: the swatch previews the component's own
                # color - the background fill for TextNoteItem, the text
                # color for PlainTextItem, or the header background for a
                # Table (its closest analog to "this item's color").
                if isinstance(first, TableItem):
                    col = QColor(first.header_bg)
                elif isinstance(first, BoardCardItem) and first is selected_sub_card and selected_sub_is_text:
                    if selected_sub.get("note_type") == "plaintext":
                        # Its only color role - see _subitem_text_color.
                        col = BoardCardItem._subitem_text_color(selected_sub)
                    else:
                        # A Text Note subitem - preview its Background
                        # fill, the color role Color now restyles for it
                        # (matching its standalone TextNoteItem
                        # counterpart) - not its text color, which is
                        # only restyled while actively editing it (see
                        # pick_color's editing_item branch).
                        col = (QColor(selected_sub.get("color"))
                               if selected_sub.get("color") else QColor(TextNoteItem.DEFAULT_COLOR))
                else:
                    default = getattr(first, "DEFAULT_COLOR", None) or "#ffffff"
                    col = QColor(first.color) if first.color else QColor(default)
                self.color_btn.setStyleSheet(f"background-color:{col.name()}; border:1px solid #888;")
                # No live text cursor to read a per-run highlight from
                # here - default the toggle off (it'll pick up the real
                # state again once actively editing/selecting text).
                self.highlight_btn.blockSignals(True)
                self.highlight_btn.setChecked(False)
                self.highlight_btn.blockSignals(False)
            self.size_slider.blockSignals(True)
            self.size_slider.setValue(int(max(1, min(40, round(font.pointSizeF())))))
            self.size_slider.blockSignals(False)
            self.size_stepper.setValue(self.size_slider.value())
            self.opacity_slider.blockSignals(True)
            self.opacity_slider.setValue(int(max(5, min(100, round(first.opacity() * 100)))))
            self.opacity_slider.blockSignals(False)
            self.opacity_stepper.setValue(self.opacity_slider.value())
            self.font_combo.blockSignals(True)
            self.font_combo.setCurrentFont(font)
            self.font_combo.blockSignals(False)
            self.bold_btn.blockSignals(True)
            self.bold_btn.setChecked(font.bold())
            self.bold_btn.blockSignals(False)
            self.italic_btn.blockSignals(True)
            self.italic_btn.setChecked(font.italic())
            self.italic_btn.blockSignals(False)
            self.underline_btn.blockSignals(True)
            self.underline_btn.setChecked(font.underline())
            self.underline_btn.blockSignals(False)
            self._set_align_button(_representative_alignment(first, editing_item))
            if editing_item is None and text_sel:
                self.link_btn.blockSignals(True)
                self.link_btn.setChecked(bool(getattr(text_sel[0], "link_url", None)))
                self.link_btn.blockSignals(False)
        elif sel:
            first = sel[0]
            if isinstance(first, DrawingItem) and first.strokes:
                col = QColor(first.strokes[-1].get("color", "#ffffff"))
                width = first.strokes[-1].get("width", 4)
            elif isinstance(first, ArrowItem):
                col = QColor(first.color) if first.color else QColor(first.DEFAULT_COLOR)
                width = first.stroke_width
            else:
                col = self.scene.brush_color
                width = self.scene.brush_width
            self.color_btn.setStyleSheet(f"background-color:{col.name()}; border:1px solid #888;")
            self.size_slider.blockSignals(True)
            self.size_slider.setValue(int(max(1, min(40, round(width)))))
            self.size_slider.blockSignals(False)
            self.size_stepper.setValue(self.size_slider.value())
            self.opacity_slider.blockSignals(True)
            self.opacity_slider.setValue(int(max(5, min(100, round(col.alphaF() * 100)))))
            self.opacity_slider.blockSignals(False)
            self.opacity_stepper.setValue(self.opacity_slider.value())
        elif other_sel:
            first = other_sel[0]
            col = QColor(first.color) if getattr(first, "color", None) else QColor(getattr(first, "DEFAULT_COLOR", None) or "#ffffff")
            self.color_btn.setStyleSheet(f"background-color:{col.name()}; border:1px solid #888;")
        elif selected_sub is not None and selected_sub.get("kind") in ("image", "gif", "video"):
            # A single-click-selected image/gif/video subitem previews
            # its own Background color here, same as its standalone
            # counterpart (see the other_sel branch above) - Top Strip
            # is its other color role but only shows in the picker
            # itself (see pick_color()), same as standalone components.
            col = QColor(selected_sub.get("color")) if selected_sub.get("color") else QColor("#1e1e1e")
            self.color_btn.setStyleSheet(f"background-color:{col.name()}; border:1px solid #888;")
        elif editing_item is None:
            self._set_brush_color(self.scene.brush_color)
            self.size_slider.blockSignals(True)
            self.size_slider.setValue(self.scene.brush_width)
            self.size_slider.blockSignals(False)
            self.size_stepper.setValue(self.size_slider.value())
            self.opacity_slider.blockSignals(True)
            self.opacity_slider.setValue(int(self.scene.brush_opacity * 100))
            self.opacity_slider.blockSignals(False)
            self.opacity_stepper.setValue(self.opacity_slider.value())

        if editing_item is not None:
            self._refresh_text_format_buttons()

    def _refresh_text_format_buttons(self):
        """Live-refresh the Font/B/I/U/Color/Link toolbar controls from
        the exact text cursor - the selected run's own formatting if
        there's a real selection, otherwise whatever's at the caret.
        Called whenever the text cursor's selection could have moved
        (see EditableTextItem.mouseReleaseEvent/keyReleaseEvent), since
        the scene's selectionChanged/focusItemChanged signals only cover
        which *item* is selected/focused, not the cursor within one that
        was already being edited."""
        editing_item = self._focused_text_item()
        if editing_item is None or not self._font_selection:
            return
        cur = editing_item.textCursor()
        fmt = cur.charFormat()
        f = fmt.font()
        self.font_combo.blockSignals(True)
        self.font_combo.setCurrentFont(f)
        self.font_combo.blockSignals(False)
        self.bold_btn.blockSignals(True)
        self.bold_btn.setChecked(f.bold())
        self.bold_btn.blockSignals(False)
        self.italic_btn.blockSignals(True)
        self.italic_btn.setChecked(f.italic())
        self.italic_btn.blockSignals(False)
        self.underline_btn.blockSignals(True)
        self.underline_btn.setChecked(f.underline())
        self.underline_btn.blockSignals(False)
        self._set_align_button(cur.blockFormat().alignment())
        size = f.pointSizeF()
        if size <= 0:
            size = editing_item.font().pointSizeF()
        self.size_slider.blockSignals(True)
        self.size_slider.setValue(int(max(1, min(40, round(size)))))
        self.size_slider.blockSignals(False)
        self.size_stepper.setValue(self.size_slider.value())
        fg = fmt.foreground()
        col = fg.color() if fg.style() != Qt.NoBrush else editing_item.defaultTextColor()
        self.color_btn.setStyleSheet(f"background-color:{col.name()}; border:1px solid #888;")
        bg = fmt.background()
        self.highlight_btn.blockSignals(True)
        self.highlight_btn.setChecked(bg.style() != Qt.NoBrush)
        self.highlight_btn.blockSignals(False)
        if bg.style() != Qt.NoBrush:
            self.highlight_color = bg.color()
        if self.link_action.isVisible():
            self.link_btn.blockSignals(True)
            self.link_btn.setChecked(fmt.isAnchor())
            self.link_btn.blockSignals(False)

    def pick_color(self):
        editing_item = self._focused_text_item()
        if editing_item is not None:
            # Editing text: a genuine selection restyles just that
            # highlighted run of characters (real per-character rich
            # text); with no selection, the whole field's text color
            # changes, same as before - never the component's own
            # background/border color while in this mode.
            parent = editing_item.parentItem()
            cur = editing_item.textCursor()
            has_sel = cur.hasSelection()
            fmt = cur.charFormat()
            fg = fmt.foreground()
            start = fg.color() if (has_sel and fg.style() != Qt.NoBrush) else editing_item.defaultTextColor()
            bg_fmt = fmt.background()
            has_highlight = bg_fmt.style() != Qt.NoBrush
            # Figure out whether this text's own component (or, inside a
            # Board Card, the specific subitem being edited - a plain
            # dict, not a live TopStripMixin instance, so it needs its
            # own lookup) has an active Top Strip, and how to persist a
            # new strip color back to whichever one it is.
            strip_start = None
            apply_strip = None
            if isinstance(parent, TopStripMixin) and parent.top_strip_enabled:
                strip_start = QColor(parent.top_strip_color)
                apply_strip = parent.set_top_strip_color
            elif (isinstance(parent, BoardCardItem) and parent._sub_edit_index is not None
                  and parent._sub_edit_index < len(parent.subitems)
                  and parent.subitems[parent._sub_edit_index].get("top_strip_enabled")):
                sub = parent.subitems[parent._sub_edit_index]
                strip_start = QColor(sub.get("top_strip_color") or TopStripMixin.DEFAULT_STRIP_COLOR)

                def apply_strip(c, _sub=sub, _parent=parent):
                    _sub["top_strip_color"] = c.name()
                    _parent.update()

            # Build one tab per color role that actually applies here -
            # Text always, plus Highlight and/or Top Strip when present -
            # so a run that has both still gets both in the SAME dialog
            # instead of one silently hiding the other.
            tabs = [("Text", start)]
            if has_highlight:
                tabs.append(("Highlight", bg_fmt.color()))
            if strip_start is not None:
                tabs.append(("Top Strip", strip_start))

            if len(tabs) > 1:
                result = open_multi_color_dialog(self, tabs, title="Pick text color")
                if result is None:
                    return
                i = 1
                color = result[0]
                hl_color = None
                if has_highlight:
                    hl_color = result[i]
                    i += 1
                strip_color = result[i] if strip_start is not None else None
                if has_highlight:
                    _apply_run_format(editing_item, has_sel, foreground=color.name(), background=hl_color.name())
                    self.highlight_color = hl_color
                else:
                    _apply_run_format(editing_item, has_sel, foreground=color.name())
                if strip_color is not None:
                    apply_strip(strip_color)
            else:
                color = QColorDialog.getColor(start, self, "Pick text color")
                if not color.isValid():
                    return
                _apply_run_format(editing_item, has_sel, foreground=color.name())
            self._restore_text_edit_focus()
            if not has_sel:
                if isinstance(parent, TextNoteItem):
                    parent.set_text_color(color)
                elif isinstance(parent, PlainTextItem):
                    parent.set_color(color)
                else:
                    editing_item.setDefaultTextColor(color)
                    if isinstance(parent, BoardCardItem) and parent._sub_edit_index is not None:
                        idx = parent._sub_edit_index
                        if idx < len(parent.subitems):
                            parent.subitems[idx]["color"] = color.name()
                            parent.update()
            self.color_btn.setStyleSheet(f"background-color:{color.name()}; border:1px solid #888;")
            return
        if self._selected_board_subitem is not None:
            # A single-click-selected Board Card subitem (not being
            # edited) - Color restyles it the exact same way it would
            # restyle its standalone counterpart: text color for a
            # "text" subitem, the Top Strip accent for image/gif/video
            # (their only other color role, mirroring the standalone
            # Image/GIF/Video/TopStripMixin components these came from).
            card, sub = self._selected_board_subitem
            kind = sub.get("kind")
            if kind == "text":
                if sub.get("note_type") == "plaintext":
                    # A plain-text subitem has just the one color role -
                    # its text color (see _subitem_text_color) - same as
                    # its standalone PlainTextItem counterpart, which
                    # isn't a TopStripMixin and so has no Background/Top
                    # Strip roles to offer here.
                    start = BoardCardItem._subitem_text_color(sub)
                    color = QColorDialog.getColor(start, self, "Pick text color")
                    if not color.isValid():
                        return
                    sub["color"] = color.name()
                    card.update()
                    self.color_btn.setStyleSheet(f"background-color:{color.name()}; border:1px solid #888;")
                    return
                # A Text Note subitem: "color" is its Background fill -
                # its actual text color lives in "text_color" and is
                # only restyled while actively editing it (see the
                # editing_item branch above) - plus Top Strip, the same
                # two color roles its standalone TextNoteItem
                # counterpart offers via Color, always shown together
                # regardless of whether the strip is currently on.
                bg_start = QColor(sub.get("color")) if sub.get("color") else QColor(TextNoteItem.DEFAULT_COLOR)
                strip_start = QColor(sub.get("top_strip_color") or TopStripMixin.DEFAULT_STRIP_COLOR)
                bg, strip = open_bg_strip_color_dialog(
                    self, bg_start, strip_start, bg_label="Background",
                )
                if bg is None:
                    return
                sub["color"] = bg.name()
                sub["top_strip_color"] = strip.name()
                card.update()
                self.color_btn.setStyleSheet(f"background-color:{bg.name()}; border:1px solid #888;")
                return
            if kind in ("image", "gif", "video"):
                # Background and Top Strip are always offered together
                # here, same as the standalone Image/GIF/Video component
                # now gets from the _other_selection branch below - the
                # checkbox (see on_top_strip_toggled) still controls
                # whether the strip actually shows, this just lets its
                # color be set/previewed at any time instead of only
                # after switching it on first.
                bg_start = QColor(sub.get("color")) if sub.get("color") else QColor("#1e1e1e")
                strip_start = QColor(sub.get("top_strip_color") or TopStripMixin.DEFAULT_STRIP_COLOR)
                bg, strip = open_bg_strip_color_dialog(
                    self, bg_start, strip_start, bg_label="Background",
                )
                if bg is None:
                    return
                sub["color"] = bg.name()
                sub["top_strip_color"] = strip.name()
                card.update()
                self.color_btn.setStyleSheet(f"background-color:{bg.name()}; border:1px solid #888;")
                return
        if self._editing_selection:
            first = self._editing_selection[0]
            if isinstance(first, DrawingItem) and first.strokes:
                start = QColor(first.strokes[-1].get("color", "#ffffff"))
            elif isinstance(first, ArrowItem):
                start = QColor(first.color) if first.color else QColor(first.DEFAULT_COLOR)
            else:
                start = self.scene.brush_color
            color = QColorDialog.getColor(start, self, "Pick color")
            if not color.isValid():
                return
            for it in self._editing_selection:
                if isinstance(it, DrawingItem):
                    it.set_stroke_style(color=color)
                elif isinstance(it, ArrowItem):
                    it.set_color(color)
            self.color_btn.setStyleSheet(f"background-color:{color.name()}; border:1px solid #888;")
            return
        if self._text_selection:
            # Whole component selected (not editing its text): change the
            # component's own color - the background fill for a Text
            # Note, or (its only color) the text color for a plain Text.
            first = self._text_selection[0]
            if isinstance(first, TopStripMixin):
                # Background and Top Strip are always offered together
                # here, regardless of whether the strip is currently
                # switched on - the checkbox (see on_top_strip_toggled)
                # still controls whether it actually shows, this just
                # lets its color be set/previewed at any time instead of
                # only after enabling it first.
                bg, strip = open_bg_strip_color_dialog(
                    self, QColor(first.color) if first.color else QColor(first.DEFAULT_COLOR),
                    QColor(first.top_strip_color), bg_label=first.COLOR_TAB_LABEL,
                )
                if bg is None:
                    return
                for it in self._text_selection:
                    it.set_color(bg)
                    if isinstance(it, TopStripMixin):
                        it.set_top_strip_color(strip)
                self.color_btn.setStyleSheet(f"background-color:{bg.name()}; border:1px solid #888;")
                return
            start = QColor(first.color) if first.color else QColor(first.DEFAULT_COLOR)
            color = QColorDialog.getColor(start, self, "Pick component color")
            if not color.isValid():
                return
            for it in self._text_selection:
                it.set_color(color)
            self.color_btn.setStyleSheet(f"background-color:{color.name()}; border:1px solid #888;")
            return
        if self._other_selection:
            # Whole component selected (Image/GIF/Video/Board Card, ...):
            # same principle - Color changes that component's own color.
            first = self._other_selection[0]
            if isinstance(first, TableItem):
                # Exception to the rule above: a table has several color
                # roles plus row/column counts, so its own "Change Color"
                # entry point (this button, and its context menu) opens
                # its dedicated settings dialog instead of QColorDialog.
                first.open_settings_dialog(self)
                return
            if isinstance(first, TopStripMixin):
                # Same as the _text_selection branch above: both color
                # roles are always offered together, independent of
                # whether Top Strip is currently switched on.
                bg, strip = open_bg_strip_color_dialog(
                    self,
                    QColor(first.color) if getattr(first, "color", None) else QColor(getattr(first, "DEFAULT_COLOR", None) or "#ffffff"),
                    QColor(first.top_strip_color), bg_label=first.COLOR_TAB_LABEL,
                )
                if bg is None:
                    return
                for it in self._other_selection:
                    it.set_color(bg)
                    if isinstance(it, TopStripMixin):
                        it.set_top_strip_color(strip)
                self.color_btn.setStyleSheet(f"background-color:{bg.name()}; border:1px solid #888;")
                return
            start = QColor(first.color) if getattr(first, "color", None) else QColor(getattr(first, "DEFAULT_COLOR", None) or "#ffffff")
            color = QColorDialog.getColor(start, self, "Pick component color")
            if not color.isValid():
                return
            for it in self._other_selection:
                it.set_color(color)
            self.color_btn.setStyleSheet(f"background-color:{color.name()}; border:1px solid #888;")
            return
        color = QColorDialog.getColor(self.scene.brush_color, self, "Pick brush color")
        if color.isValid():
            self._set_brush_color(color)

    def on_brush_type_changed(self, text):
        self.scene.brush_type = text.lower()

    def on_size_changed(self, val):
        if self._font_selection:
            editing_item = self._focused_text_item()
            for it in self._font_selection:
                _apply_text_font(it, point_size=val, editing_item=editing_item)
            return
        if self._editing_selection:
            for it in self._editing_selection:
                if isinstance(it, DrawingItem):
                    it.set_stroke_style(width=val)
                elif isinstance(it, ArrowItem):
                    it.set_stroke_width(val)
            return
        self.scene.brush_width = val

    def on_opacity_changed(self, val):
        op = val / 100.0
        if self._editing_selection:
            for it in self._editing_selection:
                if isinstance(it, DrawingItem):
                    it.set_stroke_style(opacity=op)
                elif isinstance(it, ArrowItem):
                    c = QColor(it.color) if it.color else QColor(it.DEFAULT_COLOR)
                    c.setAlpha(max(0, min(255, int(op * 255))))
                    it.color = c.name(QColor.HexArgb)
                    it.update()
            return
        if self._font_selection:
            for it in self._font_selection:
                it.setOpacity(op)
            return
        self.scene.brush_opacity = op

    # -- text formatting controls (Font / B / I / U / Link) -------------
    def on_font_family_changed(self, font):
        if not self._font_selection:
            return
        editing_item = self._focused_text_item()
        for it in self._font_selection:
            _apply_text_font(it, family=font.family(), editing_item=editing_item)
        self._restore_text_edit_focus()

    def _restore_text_edit_focus(self):
        """The font-family combo needs real keyboard focus to let you
        type/search, which silently knocks whatever text item was being
        edited out of edit mode (no click-away needed) - misleadingly
        making it look like nothing is being edited anymore, even though
        _last_edited_text_item/_font_selection still target it correctly.
        Call after such a toolbar action to hand focus straight back."""
        item = self._last_edited_text_item
        if item is None:
            return
        try:
            item.setTextInteractionFlags(Qt.TextEditorInteraction)
            item.setFocus()
        except RuntimeError:
            # The underlying Qt object was already deleted (e.g. its
            # component got removed while the combo had focus).
            self._last_edited_text_item = None

    def on_bold_toggled(self, checked):
        if not self._font_selection:
            return
        editing_item = self._focused_text_item()
        for it in self._font_selection:
            _apply_text_font(it, bold=checked, editing_item=editing_item)

    def on_italic_toggled(self, checked):
        if not self._font_selection:
            return
        editing_item = self._focused_text_item()
        for it in self._font_selection:
            _apply_text_font(it, italic=checked, editing_item=editing_item)

    def on_underline_toggled(self, checked):
        if not self._font_selection:
            return
        editing_item = self._focused_text_item()
        for it in self._font_selection:
            _apply_text_font(it, underline=checked, editing_item=editing_item)

    _ALIGN_LABELS = {Qt.AlignLeft: "Left", Qt.AlignHCenter: "Center", Qt.AlignRight: "Right"}

    def _set_align_button(self, alignment):
        """Update the Align dropdown's button text and which menu item
        shows as checked, without triggering on_align_changed (QAction's
        `triggered` signal only fires for genuine user activation, not
        programmatic setChecked(), so no signal-blocking is needed here
        the way the plain QToolButtons above need it)."""
        mask = int(alignment) & int(Qt.AlignHCenter | Qt.AlignRight)
        if mask & int(Qt.AlignHCenter):
            key = Qt.AlignHCenter
        elif mask & int(Qt.AlignRight):
            key = Qt.AlignRight
        else:
            key = Qt.AlignLeft
        act = self._align_actions.get(key)
        if act is not None:
            act.setChecked(True)
        self.align_btn.setText(f"Align: {self._ALIGN_LABELS.get(key, 'Left')}")

    def _refresh_align_button_now(self):
        """Re-derive the Align dropdown's state from the live text cursor
        the instant the popup is about to open (see its aboutToShow
        connection above) rather than trusting whatever it was already
        showing - the definitive fix for it looking "stuck" on a stale
        alignment right after clicking into a field.

        scene.focusItem() (what _focused_text_item() reads) can already
        report None by the time aboutToShow fires - opening the popup
        itself is enough to knock the scene's own idea of "focused item"
        out, same underlying issue _restore_text_edit_focus works around
        elsewhere. Falling back to _last_edited_text_item (which
        on_selection_changed keeps pointed at the real editing item for
        exactly this reason) avoids the resulting empty font_targets()
        - e.g. BoardCardItem.font_targets(None) is [] - which was making
        this look like the field had reset to Left instead of showing
        its actual alignment."""
        if not self._font_selection:
            return
        editing_item = self._focused_text_item() or self._last_edited_text_item
        first = self._font_selection[0]
        self._set_align_button(_representative_alignment(first, editing_item))

    def on_align_changed(self, alignment):
        if not self._font_selection:
            return
        # Same fallback as _refresh_align_button_now above, and for the
        # same reason: the popup menu has already been open (stealing
        # focus) by the time a user's click on one of its actions
        # actually fires this, so _focused_text_item() alone risks
        # returning None here too - which for BoardCardItem means
        # font_targets(None) == [], silently applying the new alignment
        # to nothing at all.
        editing_item = self._focused_text_item() or self._last_edited_text_item
        for it in self._font_selection:
            _apply_text_alignment(it, alignment, editing_item=editing_item)
        self._set_align_button(alignment)
        # The popup menu (like the font-family combo) genuinely needs
        # focus to be clickable at all, which otherwise silently drops
        # whatever text item was mid-edit out of edit mode - see
        # _restore_text_edit_focus.
        self._restore_text_edit_focus()

    def _apply_highlight(self, color_name):
        """Push `color_name` (or "" to clear) as the background of the
        current text selection - or, with no selection, the whole field
        - across every item in the font-format selection. Shared by the
        Text Highlight checkbox and its color-swatch button, since
        picking a new color while highlighting is already on should
        re-apply immediately, same as it does for the Color button."""
        editing_item = self._focused_text_item()
        for it in self._font_selection:
            targets = it.font_targets(editing_item) if hasattr(it, "font_targets") else [it.text_item]
            for t in targets:
                has_sel = (t is editing_item) and t.textCursor().hasSelection()
                _apply_run_format(t, has_sel, background=color_name)
        if editing_item is not None:
            self._restore_text_edit_focus()

    def on_highlight_toggled(self, checked):
        if not self._font_selection:
            return
        self._apply_highlight(self.highlight_color.name() if checked else "")

    def on_hyperlink_clicked(self):
        if not self._text_selection:
            return
        editing_item = self._focused_text_item()
        if editing_item is not None:
            # Editing text: a genuine selection turns just that run into
            # (or out of) a link; with no selection, the whole field's
            # link changes, same as the other formatting controls.
            cur = editing_item.textCursor()
            has_sel = cur.hasSelection()
            fmt = cur.charFormat()
            current = fmt.anchorHref() if fmt.isAnchor() else (
                getattr(editing_item.parentItem(), "link_url", None) or ""
            )
            url, ok = QInputDialog.getText(
                self, "Hyperlink", "URL (leave empty to remove the link):", text=current
            )
            if not ok:
                return
            url = url.strip()
            norm = normalize_link_url(url) if url else ""
            if norm:
                _apply_run_format(editing_item, has_sel, anchor_url=norm)
            else:
                # Removing the link must also drop the underline/blue
                # that were only ever applied *because* it was a link -
                # otherwise the text keeps visually looking like a link
                # even after the link itself is gone.
                _apply_run_format(editing_item, has_sel, anchor_url=None,
                                   underline=False, foreground=None)
            self._restore_text_edit_focus()
            parent = editing_item.parentItem()
            if not has_sel and hasattr(parent, "set_link"):
                was_linked = bool(getattr(parent, "link_url", None))
                parent.set_link(norm or None)
                if norm and not was_linked:
                    if isinstance(parent, PlainTextItem):
                        parent.set_color(QColor("#5b9dd9"))
                    elif isinstance(parent, TextNoteItem):
                        parent.set_text_color(QColor("#5b9dd9"))
                elif not norm and was_linked:
                    # Revert the auto-applied link-blue back to a normal
                    # color - but only if it's still exactly that color
                    # (the user hasn't since repicked something else
                    # themself via the Color button).
                    if isinstance(parent, PlainTextItem) and parent.color == "#5b9dd9":
                        parent.set_color(QColor("#ffffff"))
                    elif isinstance(parent, TextNoteItem) and parent.text_color == "#5b9dd9":
                        parent.set_text_color(QColor("#ffffff"))
            elif has_sel and norm:
                # First time this exact run becomes a link: nudge just
                # its own text to the familiar link-blue as a starting
                # point - an ordinary color choice from here on, freely
                # repickable afterward via the Color button.
                _apply_run_format(editing_item, has_sel, foreground="#5b9dd9")
            self._refresh_text_format_buttons()
            return
        first = self._text_selection[0]
        current = getattr(first, "link_url", None) or ""
        url, ok = QInputDialog.getText(
            self, "Hyperlink", "URL (leave empty to remove the link):", text=current
        )
        if not ok:
            return
        url = url.strip()
        for it in self._text_selection:
            was_linked = bool(getattr(it, "link_url", None))
            it.set_link(url or None)
            if url and not was_linked:
                # First time this item becomes a link: nudge its text
                # color to the familiar link-blue as a starting point.
                # It's an ordinary color choice from here on, so the user
                # can freely repick it afterward (via the Color button
                # while editing) and it'll still match in the exported HTML.
                if isinstance(it, PlainTextItem):
                    it.set_color(QColor("#5b9dd9"))
                elif isinstance(it, TextNoteItem):
                    it.set_text_color(QColor("#5b9dd9"))
            elif not url and was_linked:
                # Same revert as above for the in-place-edit path.
                if isinstance(it, PlainTextItem) and it.color == "#5b9dd9":
                    it.set_color(QColor("#ffffff"))
                elif isinstance(it, TextNoteItem) and it.text_color == "#5b9dd9":
                    it.set_text_color(QColor("#ffffff"))

    def on_line_style_changed(self, index):
        if not self._arrow_selection:
            return
        ls = self.line_style_combo.itemData(index)
        if not ls:
            return
        for it in self._arrow_selection:
            it.line_style = ls
            it.update()

    def on_arrow_style_changed(self, index):
        if not self._arrow_selection:
            return
        st = self.arrow_style_combo.itemData(index)
        if not st:
            return
        for it in self._arrow_selection:
            it.style = st
            it.update()

    def on_title_toggled(self, checked):
        if getattr(self, "_text_note_selection", None):
            for it in self._text_note_selection:
                if it.show_title != checked:
                    it._toggle_show_title()
            return
        sub_info = getattr(self, "_title_selected_subitem", None)
        if sub_info:
            card, sub = sub_info
            if bool(sub.get("show_title")) != checked:
                sub["show_title"] = checked
                card._autogrow_to_fit()
                card.update()

    def on_allow_board_card_toggled(self, checked):
        if not getattr(self, "_drawing_selection", None):
            return
        for it in self._drawing_selection:
            it.allow_board_card = checked

    def on_arrow_label_toggled(self, checked):
        if not self._arrow_selection:
            return
        for it in self._arrow_selection:
            if it.show_label != checked:
                it._toggle_show_label()

    def on_media_title_toggled(self, checked):
        if getattr(self, "_media_selection", None):
            for it in self._media_selection:
                if it.show_title != checked:
                    it._toggle_show_title()
            return
        sub_info = getattr(self, "_media_selected_subitem", None)
        if sub_info:
            card, sub = sub_info
            if bool(sub.get("show_title", True)) != checked:
                sub["show_title"] = checked
                card._autogrow_to_fit()
                card.update()

    def on_media_desc_toggled(self, checked):
        if getattr(self, "_media_selection", None):
            for it in self._media_selection:
                if it.show_description != checked:
                    it._toggle_show_description()
            return
        sub_info = getattr(self, "_media_selected_subitem", None)
        if sub_info:
            card, sub = sub_info
            if bool(sub.get("show_description", True)) != checked:
                sub["show_description"] = checked
                card._autogrow_to_fit()
                card.update()

    def on_top_strip_toggled(self, checked):
        if getattr(self, "_top_strip_selection", None):
            for it in self._top_strip_selection:
                if it.top_strip_enabled != checked:
                    it._toggle_top_strip()
            return
        sub_info = getattr(self, "_top_strip_selected_subitem", None)
        if sub_info:
            card, sub = sub_info
            if bool(sub.get("top_strip_enabled")) != checked:
                sub["top_strip_enabled"] = checked
                card.update()

    def on_board_link_desc_toggled(self, checked):
        if not getattr(self, "_board_link_selection", None):
            return
        for it in self._board_link_selection:
            if it.show_description != checked:
                it._toggle_show_description()

    def toggle_draw_mode(self, checked):
        self.scene.draw_mode = checked
        self.view.setDragMode(QGraphicsView.NoDrag if checked else QGraphicsView.RubberBandDrag)
        self.brush_label_action.setVisible(checked)
        self.brush_combo_action.setVisible(checked)
        self.eraser_checkbox_action.setVisible(checked)
        if not checked:
            self.eraser_checkbox.setChecked(False)
        self.statusBar().showMessage(
            "Draw mode ON \u2014 click and drag on the canvas to sketch" if checked else "Ready"
        )

    def on_eraser_toggled(self, checked):
        self.scene.erase_mode = checked
        self.statusBar().showMessage(
            "Eraser ON \u2014 drag over a sketch to erase it" if checked
            else "Draw mode ON \u2014 click and drag on the canvas to sketch"
        )

    # -- component creation ---------------------------------------------
    def _viewport_center_scene(self):
        return self.view.mapToScene(self.view.viewport().rect().center())

    def _new_component_font_dict(self, size=None, bold=False):
        d = {"font_family": self.prefs.get("default_font_family", "Segoe UI")}
        if size is not None:
            d["font_size"] = size
        d["bold"] = bold
        return d

    def _apply_default_font(self, item):
        """Apply Preferences > Default Font to a freshly created item -
        for component types (Table, Arrow) whose constructors have no
        font_family kwarg of their own, unlike Text Note/Text/media
        items which already take one directly at construction time.
        Uses the same _apply_text_font/font_targets machinery as the
        toolbar's own Font control, so this reaches every cell of a
        table or an arrow's label exactly like a manual font change
        would."""
        fam = self.prefs.get("default_font_family", "Segoe UI")
        if fam:
            _apply_text_font(item, family=fam)

    def _apply_default_title_alignment(self, item):
        """Apply the Preferences > Title Alignment default to a freshly
        created item's title - constructors take font/text/visibility as
        kwargs but have no alignment kwarg, so this is done as a small
        extra step right after construction instead."""
        ti = getattr(item, "title_item", None)
        if ti is None:
            return
        align = PREF_ALIGN_TO_QT.get(self.prefs.get("default_title_alignment", "left"), Qt.AlignLeft)
        cur = QTextCursor(ti.document())
        cur.select(QTextCursor.Document)
        bf = cur.blockFormat()
        bf.setAlignment(align)
        cur.mergeBlockFormat(bf)

    def add_text_note(self):
        pos = self._viewport_center_scene()
        fam = self.prefs.get("default_font_family", "Segoe UI")
        item = TextNoteItem(
            pos.x() - 110, pos.y() - 70,
            show_title=self.prefs.get("default_show_title", True),
            title_font=self._new_component_font_dict(
                size=self.prefs.get("default_title_font_size", 12.0), bold=True),
            font_family=fam,
        )
        self.scene.addItem(item)
        self.scene.bring_to_front(item)
        self._apply_default_title_alignment(item)

    def add_text(self):
        pos = self._viewport_center_scene()
        item = PlainTextItem(
            pos.x() - 110, pos.y() - 25,
            font_family=self.prefs.get("default_font_family", "Segoe UI"),
        )
        self.scene.addItem(item)
        self.scene.bring_to_front(item)

    def add_board_card(self):
        pos = self._viewport_center_scene()
        item = BoardCardItem(
            pos.x() - 140, pos.y() - 160,
            title_font=self._new_component_font_dict(
                size=self.prefs.get("default_title_font_size", 12.0), bold=True),
        )
        self.scene.addItem(item)
        self.scene.bring_to_front(item)
        self._apply_default_title_alignment(item)

    def add_board_link(self):
        """Create a shortcut card on the current board pointing at another
        board .html file in the same project folder (creating that file
        if it doesn't exist yet, or wiring up to it if it does) - see
        BoardLinkItem for the resulting card and its right-click menu."""
        if not self._ensure_project_and_file():
            return

        dlg = BoardLinkCreateDialog(self)
        if dlg.exec() != QDialog.Accepted:
            return
        safe_name = sanitize_board_filename(dlg.board_name())
        target_file = safe_name + ".html"
        project_dir = os.path.dirname(self.current_file)
        target_path = os.path.join(project_dir, target_file)
        new_breadcrumb = self.breadcrumb + [{"name": safe_name, "file": target_file}]

        if os.path.exists(target_path):
            box = QMessageBox(self)
            box.setWindowTitle("Board already exists")
            box.setText(
                f"A board file named \u201c{target_file}\u201d already exists in this "
                "project folder.\n\nOverwrite it with a brand-new empty board, or "
                "use the existing board as the target of this shortcut?"
            )
            overwrite_btn = box.addButton("Overwrite", QMessageBox.DestructiveRole)
            use_existing_btn = box.addButton("Use Existing", QMessageBox.AcceptRole)
            box.addButton(QMessageBox.Cancel)
            box.exec()
            clicked = box.clickedButton()
            if clicked == overwrite_btn:
                self._write_board_file(target_path, {"items": []}, new_breadcrumb)
            elif clicked == use_existing_btn:
                try:
                    with open(target_path, "r", encoding="utf-8") as f:
                        existing_data = extract_scene_data(f.read()) or {"items": []}
                except Exception as e:
                    QMessageBox.critical(self, "Error", f"Could not read existing board: {e}")
                    return
                # Re-parent the existing board under this board's path -
                # "its path inside will be updated", per spec.
                self._write_board_file(target_path, existing_data, new_breadcrumb)
            else:
                return
        else:
            self._write_board_file(target_path, {"items": []}, new_breadcrumb)

        pos = self._viewport_center_scene()
        item = BoardLinkItem(
            pos.x() - 110, pos.y() - 60, title=safe_name, target_file=target_file,
            thumb_mime=dlg.thumb_mime, thumb_data=dlg.thumb_data,
        )
        self.scene.addItem(item)
        self.scene.bring_to_front(item)
        self.statusBar().showMessage(f"Linked board: {target_file}", 4000)

    def _write_board_file(self, path, data, breadcrumb):
        """Write a board's JSON `data` out to `path` as a standalone HTML
        file, stamping it with `breadcrumb` (its own full nested-boards
        path) - used both for the currently-open board (_write_html) and
        for sibling board files created/re-parented by add_board_link."""
        data = dict(data)
        data["breadcrumb"] = breadcrumb
        html = build_html_document(data)
        with open(path, "w", encoding="utf-8") as f:
            f.write(html)

    def add_table(self):
        pos = self._viewport_center_scene()
        item = TableItem(pos.x() - 180, pos.y() - 100)
        self.scene.addItem(item)
        self.scene.bring_to_front(item)
        self._apply_default_font(item)

    def add_image(self):
        path, _ = QFileDialog.getOpenFileName(self, "Select image", "", "Images (*.png *.jpg *.jpeg *.bmp *.webp)")
        if path:
            self.create_item_from_file(path, self._viewport_center_scene())

    def add_gif(self):
        path, _ = QFileDialog.getOpenFileName(self, "Select GIF", "", "GIF (*.gif)")
        if path:
            self.create_item_from_file(path, self._viewport_center_scene())

    def add_video(self):
        path, _ = QFileDialog.getOpenFileName(self, "Select video", "", "Video (*.mp4 *.mov *.avi *.webm *.mkv)")
        if path:
            self.create_item_from_file(path, self._viewport_center_scene())

    def add_arrow(self, style="single"):
        center = self._viewport_center_scene()
        p1 = QPointF(center.x() - 80, center.y() + 40)
        p2 = QPointF(center.x() + 80, center.y() - 40)
        item = ArrowItem.from_scene_points(
            p1, p2,
            color=self.scene.brush_color.name(),
            stroke_width=self.prefs.get("default_arrow_size", 4),
            style=style,
        )
        self.scene.addItem(item)
        self.scene.bring_to_front(item)
        self.scene.clearSelection()
        item.setSelected(True)
        self._apply_default_font(item)

    def create_item_from_file(self, path, scene_pos):
        ext = os.path.splitext(path)[1].lower()
        try:
            with open(path, "rb") as f:
                data = f.read()
        except Exception as e:
            QMessageBox.warning(self, "Error", f"Could not read file: {e}")
            return None
        show_title = self.prefs.get("default_show_title", True)
        show_desc = self.prefs.get("default_show_description", True)
        title_font = self._new_component_font_dict(
            size=self.prefs.get("default_title_font_size", 12.0), bold=True)
        desc_font = self._new_component_font_dict(
            size=self.prefs.get("default_description_font_size", 9.0))
        if ext in GIF_EXTS:
            item = GifItem(scene_pos.x() - 120, scene_pos.y() - 90, gif_bytes=data,
                            title="Title", description="description...",
                            show_title=show_title, show_description=show_desc,
                            title_font=title_font, desc_font=desc_font)
        elif ext in VIDEO_EXTS:
            item = VideoItem(scene_pos.x() - 160, scene_pos.y() - 110, video_bytes=data,
                              title="Title", description="description...",
                              show_title=show_title, show_description=show_desc,
                              title_font=title_font, desc_font=desc_font)
        elif ext in IMAGE_EXTS:
            pm = QPixmap()
            pm.loadFromData(data)
            item = ImageItem(scene_pos.x() - 120, scene_pos.y() - 90, pixmap=pm,
                              title="Title", description="description...",
                              show_title=show_title, show_description=show_desc,
                              title_font=title_font, desc_font=desc_font)
        else:
            QMessageBox.information(self, "Unsupported file", f"Unsupported file type: {ext}")
            return None
        self.scene.addItem(item)
        self.scene.bring_to_front(item)
        self._apply_default_title_alignment(item)
        return item

    # -- preferences -------------------------------------------------------
    def open_preferences(self):
        dlg = PreferencesDialog(self)
        dlg.exec()

    def apply_font_to_all_boards(self, family):
        """Set every component's font to `family` on the board currently
        open AND every other .html board file living in the same project
        folder (BoardLink shortcuts only ever point at sibling files
        there - see _ensure_project_and_file/add_board_link). Returns how
        many board files were updated in total."""
        count = 0

        # Current board: round-trip through serialize -> mutate -> load,
        # the same path used by undo/open, so every component type and
        # board-card subitem is rebuilt exactly the way it always is
        # instead of needing to poke each live Qt item's font by hand.
        data = self.scene.serialize()
        replace_all_font_families(data, family)
        self.scene.load(data)
        self._reset_undo_history()
        self._update_saved_snapshot()
        if self.current_file:
            self._write_html(self.current_file)
        count += 1

        project_dir = self.project_dir or (os.path.dirname(self.current_file) if self.current_file else None)
        if project_dir and os.path.isdir(project_dir):
            current_name = os.path.basename(self.current_file) if self.current_file else None
            for name in os.listdir(project_dir):
                if not name.lower().endswith(".html") or name == current_name:
                    continue
                path = os.path.join(project_dir, name)
                try:
                    with open(path, "r", encoding="utf-8") as f:
                        html = f.read()
                    file_data = extract_scene_data(html)
                    if file_data is None:
                        continue
                    replace_all_font_families(file_data, family)
                    new_html = build_html_document(file_data)
                    with open(path, "w", encoding="utf-8") as f:
                        f.write(new_html)
                    count += 1
                except Exception:
                    continue

        self.prefs["default_font_family"] = family
        save_app_preferences(self.prefs)
        self.statusBar().showMessage(f"Applied font \u201c{family}\u201d to {count} board file(s)", 4000)
        return count

    # -- clipboard ops -----------------------------------------------------
    def copy_selection(self):
        items = [it for it in self.scene.selectedItems() if isinstance(it, BaseComponentItem)]
        self.clipboard_data = [it.serialize() for it in items]

    def paste_clipboard(self):
        if self.clipboard_data:
            self.scene.clearSelection()
            offset = 30
            for d in self.clipboard_data:
                nd = dict(d)
                nd["id"] = new_id()
                nd["x"] = d["x"] + offset
                nd["y"] = d["y"] + offset
                item = deserialize_component(nd)
                if item:
                    self.scene.addItem(item)
                    self.scene.bring_to_front(item)
                    item.setSelected(True)
            return
        # fall back to OS clipboard image
        cb = QApplication.clipboard()
        img = cb.image()
        if img is not None and not img.isNull():
            pos = self._viewport_center_scene()
            item = ImageItem(pos.x() - 120, pos.y() - 90, pixmap=QPixmap.fromImage(img),
                              title="Title", description="description...")
            self.scene.addItem(item)
            self.scene.bring_to_front(item)

    def duplicate_selection(self):
        items = [it for it in self.scene.selectedItems() if isinstance(it, BaseComponentItem)]
        self.scene.clearSelection()
        for it in items:
            d = it.serialize()
            d["id"] = new_id()
            d["x"] = it.pos().x() + 25
            d["y"] = it.pos().y() + 25
            new_item = deserialize_component(d)
            if new_item:
                self.scene.addItem(new_item)
                self.scene.bring_to_front(new_item)
                new_item.setSelected(True)

    def delete_selection(self):
        if self._selected_board_subitem is not None:
            # A single-click-selected Board Card subitem, not a real
            # scene selection - remove it from its card's own subitems
            # list instead (scene.selectedItems() wouldn't include it at
            # all - see the comment above board_text_sel's computation
            # in on_selection_changed for why).
            card, sub = self._selected_board_subitem
            try:
                idx = card.subitems.index(sub)
            except ValueError:
                idx = None
            if idx is not None:
                card.subitems.pop(idx)
                if card._selected_sub_index is not None and card._selected_sub_index > idx:
                    card._selected_sub_index -= 1
                card._prune_video_proxies()
                card._prune_gif_movies()
                card._prune_rich_doc_cache()
                card._prune_image_pixmap_cache()
                card._prune_subitem_scaled_cache()
                card._autogrow_to_fit()
            self.scene.clear_board_subitem_selection()
            self.on_selection_changed()
            return
        for it in list(self.scene.selectedItems()):
            self.scene.removeItem(it)

    def keyPressEvent(self, event):
        if event.key() in (Qt.Key_Delete, Qt.Key_Backspace):
            focus_item = self.scene.focusItem()
            if not isinstance(focus_item, QGraphicsTextItem):
                self.delete_selection()
        super().keyPressEvent(event)

    # -- unsaved-changes tracking -----------------------------------------
    # -- undo / redo -------------------------------------------------
    def _on_scene_changed_for_undo(self, *args):
        """Any visual change to the scene (move/resize/type/draw/delete/
        property edit) lands here. Restarting the single-shot timer on
        every call is the debounce: a burst of changes (a drag, a
        typing run, a freehand stroke) keeps pushing the commit back
        until things go quiet for MAX_UNDO_STEPS's sibling interval, at
        which point _commit_undo_checkpoint turns it into one undo
        step. Ignored while undo()/redo() itself is loading a snapshot,
        so restoring history doesn't recursively add to it."""
        if self._undo_restoring:
            return
        self._undo_commit_timer.start()

    def _flush_pending_undo_checkpoint(self):
        """Commit right away if a checkpoint is already pending, instead
        of waiting out the rest of the debounce - called on selection/
        focus changes so e.g. clicking off a just-edited text note or
        onto a different item commits that edit immediately. A no-op
        (and cheap) when nothing is pending, e.g. a plain click that
        didn't change anything."""
        if self.scene.rubber_band_dragging:
            # Skipped mid-drag - _commit_undo_checkpoint below would
            # JSON-serialize the whole board, and this can otherwise run
            # dozens of times a second during a rubber-band drag. Called
            # once for real right after the drag ends (see MindMapView).
            return
        if self._undo_commit_timer.isActive():
            self._commit_undo_checkpoint()

    def _commit_undo_checkpoint(self):
        if self._undo_restoring:
            return
        self._undo_commit_timer.stop()
        snapshot = self._current_snapshot()
        if snapshot is None:
            return
        if self._undo_baseline is None:
            self._undo_baseline = snapshot
            return
        if snapshot == self._undo_baseline:
            return  # nothing actually changed (e.g. just a hover/selection repaint)
        self._undo_stack.append(self._undo_baseline)
        if len(self._undo_stack) > self.MAX_UNDO_STEPS:
            self._undo_stack.pop(0)
        self._undo_baseline = snapshot
        self._redo_stack.clear()
        self._update_undo_redo_actions()

    def _reset_undo_history(self, snapshot=None):
        """Start a fresh undo timeline at the current board state - used
        at startup and whenever the board content is replaced wholesale
        (New Board, New Project, Open, navigating to another board)
        rather than edited in place. Pass a precomputed `snapshot` when
        the caller already has one (e.g. _load_board_file) to avoid
        serializing the whole board a second time."""
        self._undo_commit_timer.stop()
        self._undo_stack = []
        self._redo_stack = []
        self._undo_baseline = snapshot if snapshot is not None else self._current_snapshot()
        self._update_undo_redo_actions()

    def _update_undo_redo_actions(self):
        self.undo_action.setEnabled(bool(self._undo_stack))
        self.redo_action.setEnabled(bool(self._redo_stack))

    def _reset_transient_item_refs(self):
        """Null out every MainWindow-side reference that can point
        directly at a component (or one of its child text items) -
        called right before scene.load() wholesale-replaces the board's
        contents (a fresh Open/navigate, or an undo/redo), so nothing is
        left dangling at a destroyed item once clear_board()'s own
        local references (the only thing keeping such items alive
        through the teardown) go out of scope. See _load_board_file for
        the fuller explanation of why this matters."""
        self._last_edited_text_item = None
        self._active_label_arrow = None
        self._active_text_board_card = None
        self._selected_board_subitem = None
        if self.scene is not None:
            self.scene._subitem_selected_card = None
        self._text_selection = None
        self._font_selection = None
        self._arrow_selection = None
        self._other_selection = None
        self._text_note_selection = None
        self._media_selection = None
        self._top_strip_selection = None
        self._top_strip_selected_subitem = None

    def _restore_undo_snapshot(self, snapshot_json):
        self._undo_restoring = True
        try:
            data = json.loads(snapshot_json)
            self.scene.clearSelection()
            self._reset_transient_item_refs()
            self.scene.load(data)
        finally:
            self._undo_restoring = False
        self._undo_baseline = snapshot_json
        self._update_undo_redo_actions()
        self._refresh_title_bar()

    def undo(self):
        # Flush any not-yet-committed change first, so e.g. pressing
        # Ctrl+Z right after finishing a drag (before the debounce timer
        # has fired) undoes that drag rather than skipping straight past
        # it to whatever came before.
        self._flush_pending_undo_checkpoint()
        if not self._undo_stack:
            return
        self._redo_stack.append(self._undo_baseline)
        prev = self._undo_stack.pop()
        self._restore_undo_snapshot(prev)
        self.statusBar().showMessage("Undo", 2000)

    def redo(self):
        if not self._redo_stack:
            return
        self._undo_stack.append(self._undo_baseline)
        nxt = self._redo_stack.pop()
        self._restore_undo_snapshot(nxt)
        self.statusBar().showMessage("Redo", 2000)

    def _current_snapshot(self):
        """A JSON snapshot of the board's actual content - used only for
        comparing against _saved_snapshot, never actually written
        anywhere itself. Deliberately excludes the view (pan/zoom) state
        that _write_html also saves: just scrolling or zooming the canvas
        isn't a "change" worth nagging the user to save."""
        try:
            return json.dumps(self.scene.serialize(), sort_keys=True)
        except Exception:
            # If anything about the scene is in a state that can't be
            # serialized (shouldn't normally happen), don't let that
            # crash the app or block closing over it - just treat it as
            # "can't tell", which _has_unsaved_changes below reads as
            # "nothing to warn about".
            return None

    def _update_saved_snapshot(self, snapshot=None):
        self._saved_snapshot = snapshot if snapshot is not None else self._current_snapshot()
        self._refresh_title_bar()

    def _has_unsaved_changes(self):
        current = self._current_snapshot()
        if current is None or self._saved_snapshot is None:
            return False
        return current != self._saved_snapshot

    def _confirm_discard_changes(self, title="Unsaved changes"):
        """Ask whether to save, discard, or cancel before an action that
        would lose the current board's unsaved changes (closing the
        window, opening/navigating to a different board, clearing the
        board for a new one). Returns True if it's safe to proceed."""
        if not self._has_unsaved_changes():
            return True
        resp = QMessageBox.question(
            self, title,
            "This board has unsaved changes. Save them before continuing?",
            QMessageBox.Save | QMessageBox.Discard | QMessageBox.Cancel,
            QMessageBox.Save,
        )
        if resp == QMessageBox.Cancel:
            return False
        if resp == QMessageBox.Save:
            self.save_board()
            # save_board() falls back to Save As when there's no
            # current_file yet - if the user then cancels *that* dialog,
            # nothing actually got saved, so treat it the same as Cancel
            # rather than continuing to lose the changes.
            return not self._has_unsaved_changes()
        return True  # Discard

    def closeEvent(self, event):
        if self._confirm_discard_changes(title="Quit OpenNote"):
            event.accept()
        else:
            event.ignore()

    # -- file save / load -----------------------------------------------
    def new_board(self):
        if not self._confirm_discard_changes(title="New board"):
            return
        if QMessageBox.question(self, "New board", "Clear the current board?") == QMessageBox.Yes:
            self.scene.clear_board()
            self.current_file = None
            self.breadcrumb = [{"name": "Untitled", "file": None}]
            self._update_breadcrumb_bar()
            self._set_base_title("OpenNote \u2014 Milanote-style Mind Map")
            self._update_saved_snapshot()
            self._reset_undo_history()

    def new_project(self):
        """Start a brand-new project: clear the board, then immediately
        ask for a project folder (existing or newly created) and a name
        for this first board file inside it - see
        choose_or_create_project_folder/_ensure_project_and_file, and
        BoardLinkItem for how sibling boards later attach to that same
        folder."""
        if not self._confirm_discard_changes(title="New project"):
            return
        if self.scene.items() and QMessageBox.question(
            self, "New project", "Clear the current board and start a new project?"
        ) != QMessageBox.Yes:
            return
        self.scene.clear_board()
        self.current_file = None
        self.project_dir = None
        self.breadcrumb = [{"name": "Untitled", "file": None}]
        self._update_breadcrumb_bar()
        self._ensure_project_and_file()
        self._update_saved_snapshot()
        self._reset_undo_history()

    def choose_or_create_project_folder(self, title="Choose Project Folder"):
        """Ask the user to pick an existing folder - or create a new one -
        to hold a project's board .html files (every board of a project
        lives flat inside one shared folder, see BoardLinkItem). Returns
        the chosen absolute path, or None if the user cancelled. The
        native directory-picker dialog already has its own "Create New
        Folder" control, so creating a not-yet-existing folder and
        selecting it happens in the same step."""
        dlg = QFileDialog(self, title)
        dlg.setFileMode(QFileDialog.Directory)
        dlg.setOption(QFileDialog.ShowDirsOnly, True)
        if dlg.exec() != QDialog.Accepted:
            return None
        selected = dlg.selectedFiles()
        folder = selected[0] if selected else None
        if folder and not os.path.isdir(folder):
            try:
                os.makedirs(folder, exist_ok=True)
            except Exception as e:
                QMessageBox.critical(self, "Could not create folder", str(e))
                return None
        return folder

    def _ensure_project_and_file(self):
        """Make sure the board currently on screen is saved somewhere
        inside a project folder, prompting the user to choose or create
        that folder - and then a file name inside it - if it isn't
        already saved. Every other board .html file belonging to this
        project (created via Board Link cards) will live flat alongside
        this one, in that same folder. Returns True once self.current_file
        points at a real saved file, False if the user cancelled at any
        point."""
        if self.current_file:
            return True
        QMessageBox.information(
            self, "Choose a project folder",
            "Boards are saved as .html files inside a single project "
            "folder (board shortcuts link to sibling files there), so "
            "pick or create that folder now to save this board."
        )
        folder = self.choose_or_create_project_folder("Choose or Create Project Folder")
        if not folder:
            return False
        default_name = (self.breadcrumb[-1].get("name") if self.breadcrumb else None) or "Main"
        name, ok = QInputDialog.getText(
            self, "Board file name", "File name for this board:", text=default_name
        )
        if not ok or not name.strip():
            return False
        safe_name = sanitize_board_filename(name)
        basename = safe_name + ".html"
        path = os.path.join(folder, basename)
        if os.path.exists(path) and QMessageBox.question(
            self, "File exists",
            f"\u201c{basename}\u201d already exists in this folder. Overwrite it?",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.No,
        ) != QMessageBox.Yes:
            return False

        if self.breadcrumb:
            self.breadcrumb[-1] = {"name": safe_name, "file": basename}
        else:
            self.breadcrumb = [{"name": safe_name, "file": basename}]
        self.project_dir = folder
        self._write_html(path)
        self.current_file = path
        self._set_base_title(f"OpenNote \u2014 {basename}")
        self._update_breadcrumb_bar()
        return True

    def save_board(self):
        if self.current_file:
            self._write_html(self.current_file)
        else:
            self.save_board_as()

    def save_board_as(self):
        start_dir = self.project_dir or (os.path.dirname(self.current_file) if self.current_file else "")
        start_path = os.path.join(start_dir, "board.html") if start_dir else "board.html"
        path, _ = QFileDialog.getSaveFileName(self, "Save board as HTML", start_path, "HTML files (*.html)")
        if path:
            if not path.lower().endswith(".html"):
                path += ".html"
            basename = os.path.basename(path)
            # Keep this board's own breadcrumb segment (the last one) in
            # sync with wherever it's actually being saved - matters most
            # for the very first save, where it still says "Untitled".
            name = os.path.splitext(basename)[0]
            if self.breadcrumb:
                self.breadcrumb[-1] = {"name": name, "file": basename}
            else:
                self.breadcrumb = [{"name": name, "file": basename}]
            self._write_html(path)
            self.current_file = path
            self.project_dir = os.path.dirname(path)
            self._set_base_title(f"OpenNote \u2014 {basename}")
            self._update_breadcrumb_bar()

    def rename_main_board(self):
        """File > Refactor (Rename) Main Board: renames the project's
        root board (breadcrumb[0] - the very first board of this
        project, the one every other board's breadcrumb chain ultimately
        traces back to) and rewrites every reference to it - board_link
        cards and breadcrumb segments - across every sibling .html file
        in the project folder, plus its own filename on disk, so nothing
        is left pointing at the old name."""
        if not self.current_file or not self.project_dir or not self.breadcrumb:
            QMessageBox.information(
                self, "Cannot rename",
                "Save this board first so it belongs to a project folder."
            )
            return
        proj = self.project_dir
        root_seg = self.breadcrumb[0]
        old_target_file = root_seg.get("file")
        if not old_target_file:
            QMessageBox.information(
                self, "Cannot rename", "The main board hasn't been saved yet."
            )
            return
        old_path = os.path.join(proj, old_target_file)
        is_current = os.path.normpath(self.current_file) == os.path.normpath(old_path)
        if not is_current and not os.path.exists(old_path):
            QMessageBox.warning(
                self, "Cannot rename", "The main board file could not be found on disk."
            )
            return

        old_name_no_ext = os.path.splitext(old_target_file)[0]
        new_name, ok = QInputDialog.getText(
            self, "Rename main board", "New board name:", text=old_name_no_ext
        )
        if not ok or not new_name.strip():
            return
        safe_new_name = sanitize_board_filename(new_name)
        new_target_file = safe_new_name + ".html"
        if new_target_file == old_target_file:
            return
        new_path = os.path.join(proj, new_target_file)
        if os.path.exists(new_path):
            QMessageBox.warning(
                self, "Rename failed",
                f"A file named \u201c{new_target_file}\u201d already exists in the project folder.",
            )
            return

        # 1. Write the renamed root board's own file. If it's the board
        #    currently open on screen, save straight from the live scene
        #    (so this also carries over any not-yet-saved edits) instead
        #    of whatever's on disk; otherwise it isn't loaded anywhere
        #    right now, so just read, retarget, and rewrite it in place.
        self.breadcrumb[0] = {"name": safe_new_name, "file": new_target_file}
        try:
            if is_current:
                data = self.scene.serialize()
                data["view"] = self.view.current_view_state()
                data["breadcrumb"] = self.breadcrumb
                with open(new_path, "w", encoding="utf-8") as f:
                    f.write(build_html_document(data))
                if os.path.exists(old_path) and os.path.normpath(old_path) != os.path.normpath(new_path):
                    os.remove(old_path)
                self.current_file = new_path
                self._set_base_title(f"OpenNote \u2014 {new_target_file}")
            else:
                os.rename(old_path, new_path)
                with open(new_path, "r", encoding="utf-8") as f:
                    data = extract_scene_data(f.read()) or {"items": []}
                breadcrumb = data.get("breadcrumb") or [{}]
                breadcrumb[0] = {"name": safe_new_name, "file": new_target_file}
                data["breadcrumb"] = breadcrumb
                with open(new_path, "w", encoding="utf-8") as f:
                    f.write(build_html_document(data))
        except Exception as e:
            QMessageBox.critical(self, "Rename failed", str(e))
            return

        # 2. Walk every other sibling .html file in the project and fix
        #    up any board_link card or breadcrumb segment still pointing
        #    at the old root filename/name.
        updated = _apply_rename_to_project_siblings(
            proj, old_target_file, old_name_no_ext, new_target_file, safe_new_name,
            skip_path=new_path,
        )

        # 3. If the board currently on screen isn't the root itself, its
        #    own in-memory breadcrumb (an ancestor entry, since it's a
        #    descendant of the root) and any BoardLinkItem cards on
        #    screen pointing at the old root filename need the same fix
        #    applied live, then persist that board too.
        if not is_current:
            for i, seg in enumerate(self.breadcrumb):
                if seg.get("file") == old_target_file:
                    self.breadcrumb[i] = {"name": safe_new_name, "file": new_target_file}
            for it in self.scene.items():
                if isinstance(it, BoardLinkItem) and it.target_file == old_target_file:
                    it.target_file = new_target_file
                    if it.title == old_name_no_ext:
                        it.title = safe_new_name
                    it.mark_count_stale()
            if self.current_file:
                self._write_html(self.current_file)

        self._update_breadcrumb_bar()
        self.statusBar().showMessage(
            f"Renamed main board to \u201c{new_target_file}\u201d ({updated} other file(s) updated)", 5000
        )

    def _write_html(self, path):
        data = self.scene.serialize()
        data["view"] = self.view.current_view_state()
        data["breadcrumb"] = self.breadcrumb
        html = build_html_document(data)
        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write(html)
            self.statusBar().showMessage(f"Saved: {path}", 4000)
            self._update_saved_snapshot()
            self._add_recent_file(path)
        except Exception as e:
            QMessageBox.critical(self, "Save failed", str(e))

    # -- File > Recent -----------------------------------------------------
    def _get_recent_files(self):
        """Up to MAX_RECENT_FILES most-recently opened/saved board paths,
        most recent first - persisted via QSettings (see
        _add_recent_file) so the list survives across runs. Entries whose
        file no longer exists on disk are silently dropped here rather
        than shown as a dead menu item."""
        s = QSettings("OpenNote", "OpenNote")
        files = s.value(RECENT_FILES_SETTINGS_KEY, [])
        if isinstance(files, str):
            files = [files]
        return [f for f in files if f and os.path.exists(f)]

    def _add_recent_file(self, path):
        """Push `path` to the front of the Recent list, de-duplicating
        against any existing entry for the same file and capping the
        list at MAX_RECENT_FILES - called after every successful open
        (_load_board_file) and save (_write_html)."""
        path = os.path.normpath(os.path.abspath(path))
        files = [os.path.normpath(f) for f in self._get_recent_files()]
        files = [f for f in files if f != path]
        files.insert(0, path)
        files = files[:MAX_RECENT_FILES]
        QSettings("OpenNote", "OpenNote").setValue(RECENT_FILES_SETTINGS_KEY, files)

    def _rebuild_recent_menu(self):
        """Repopulate File > Recent right before it's shown (see
        file_menu.aboutToShow in _build_menu), so it always reflects the
        latest list instead of going stale between opens/saves."""
        self.recent_menu.clear()
        files = self._get_recent_files()
        if not files:
            empty_act = self.recent_menu.addAction("No recent boards")
            empty_act.setEnabled(False)
            return
        for path in files:
            act = self.recent_menu.addAction(os.path.basename(path))
            act.setToolTip(path)
            act.triggered.connect(lambda checked=False, p=path: self._open_recent_file(p))

    def _open_recent_file(self, path):
        if not os.path.exists(path):
            QMessageBox.warning(self, "Open failed", f"This board no longer exists:\n{path}")
            return
        if not self._confirm_discard_changes(title="Open board"):
            return
        self._load_board_file(path, error_title="Open failed")

    def open_board(self):
        if not self._confirm_discard_changes(title="Open board"):
            return
        path, _ = QFileDialog.getOpenFileName(self, "Open board", "", "HTML files (*.html)")
        if not path:
            return
        self._load_board_file(path, error_title="Open failed")

    def open_dropped_board(self, path):
        """Open an .html board file dropped onto the window - same
        behavior as File > Open... (confirms discarding unsaved changes,
        then loads it). Shared by MainWindow's own dropEvent (drops
        landing on the toolbar/breadcrumb bar) and MindMapView's
        dropEvent (drops landing on the canvas itself)."""
        if not self._confirm_discard_changes(title="Open board"):
            return
        self._load_board_file(path, error_title="Open failed")

    # -- drag & drop (dropping an .html board file opens it, same as
    # File > Open...) ---------------------------------------------------
    def _dropped_html_path(self, event):
        """Return the local path of the first .html file among the
        event's dropped URLs, or None if there isn't one."""
        if not event.mimeData().hasUrls():
            return None
        for url in event.mimeData().urls():
            if not url.isLocalFile():
                continue
            path = url.toLocalFile()
            if path.lower().endswith(".html"):
                return path
        return None

    def dragEnterEvent(self, event):
        if self._dropped_html_path(event) is not None:
            event.acceptProposedAction()
        else:
            super().dragEnterEvent(event)

    def dragMoveEvent(self, event):
        if self._dropped_html_path(event) is not None:
            event.acceptProposedAction()
        else:
            super().dragMoveEvent(event)

    def dropEvent(self, event):
        path = self._dropped_html_path(event)
        if path is None:
            super().dropEvent(event)
            return
        event.acceptProposedAction()
        self.open_dropped_board(path)

    def navigate_to_file(self, path):
        """Switch the whole window to display a different board .html
        file - used by BoardLinkItem (double-click / "Open Board") and by
        clicking an ancestor segment in the breadcrumb bar. Unsaved
        changes on the current board are not auto-saved first (consistent
        with the rest of the app - Ctrl+S / the Save action is what
        persists changes), so the user is asked if there's anything to
        lose."""
        path = os.path.normpath(path)
        if self.current_file and os.path.normpath(self.current_file) == path:
            return
        if not self._confirm_discard_changes(title="Navigate away"):
            return
        self._load_board_file(path, error_title="Navigation failed")

    # -- status bar: zoom % (bottom-right) and board-load progress
    # (bottom-left) --------------------------------------------------------
    def _update_zoom_label(self):
        """Refresh the permanent bottom-right status bar label with the
        view's current zoom level. Called from MindMapView after every
        place the view's scale actually changes (Ctrl+Wheel zoom and
        apply_view_state, which restores a board's saved zoom/pan) rather
        than polled, since QGraphicsView has no transform-changed signal
        to hook into."""
        pct = round(self.view.transform().m11() * 100)
        self.zoom_label.setText(f"Zoom: {pct}%")

    def _set_loading_progress_label(self, board_name, pct):
        """Update (or, with board_name=None, clear) the permanent
        bottom-left status bar label used while a board is loading. Kept
        separate from _on_board_load_progress so _load_board_file can
        also use it for the very first (0%) and final (cleared) states
        without going through the done/total percentage math."""
        if board_name is None:
            self.loading_label.clear()
        else:
            self.loading_label.setText(f"Loading {board_name}\u2026 {pct}%")
        # scene.load() below is one long synchronous call - without
        # pumping the event loop here the label text above would just
        # sit in Qt's paint queue and never actually reach the screen
        # until loading was already finished, defeating the point of a
        # progress indicator.
        QApplication.processEvents()

    def _on_board_load_progress(self, board_name, done, total):
        """progress_callback passed to MindMapScene.load - see there.
        Throttled by elapsed wall-clock time (not percentage) so it
        repaints often enough to actually be visible on a large, slow
        board without paying a processEvents() call per item on a huge
        one - and, crucially, so a small/fast board (most boards: the
        whole load finishes in a handful of milliseconds) doesn't try to
        force multiple repaints into a window shorter than a single
        frame. There is nothing wrong with the label barely flashing on
        those - the load genuinely is closer to instant than the ~16ms
        it'd take to even see it."""
        now = time.perf_counter()
        is_last = done >= total
        if not is_last and (now - self._loading_progress_last_paint) < 0.05:
            return
        self._loading_progress_last_paint = now
        pct = int(done * 100 / total) if total else 100
        if pct == self._loading_progress_shown_pct:
            return
        self._loading_progress_shown_pct = pct
        self._set_loading_progress_label(board_name, pct)

    def _load_board_file(self, path, error_title="Open failed"):
        try:
            with open(path, "r", encoding="utf-8") as f:
                html = f.read()
            data = extract_scene_data(html)
            if data is None:
                QMessageBox.warning(self, error_title, "No board data found in this HTML file.")
                return
            # See _reset_transient_item_refs's docstring: scene.load()
            # below only protects the scene's *own* selection/focus
            # (MindMapScene.clear_board) - it has no way to know about
            # these MainWindow-side "sticky" references left pointing
            # at a component that's about to be destroyed, which is
            # what actually crashed the app on navigating away rather
            # than just misbehaving.
            self._reset_transient_item_refs()
            basename_for_progress = os.path.basename(path)
            self._loading_progress_shown_pct = -1
            self._loading_progress_last_paint = 0.0
            self._set_loading_progress_label(basename_for_progress, 0)
            n_items = len(data.get("items", []))
            _load_t0 = time.perf_counter()
            try:
                self.scene.load(
                    data,
                    progress_callback=lambda done, total, name=basename_for_progress:
                        self._on_board_load_progress(name, done, total),
                )
            finally:
                self._set_loading_progress_label(None, None)
            if _PERF_DEBUG:
                elapsed_ms = (time.perf_counter() - _load_t0) * 1000
                print(f"[PERF] scene.load(): {n_items} items in {elapsed_ms:.1f} ms "
                      f"({elapsed_ms / n_items:.3f} ms/item)" if n_items else
                      f"[PERF] scene.load(): 0 items in {elapsed_ms:.1f} ms",
                      file=sys.stderr)
            self.view.apply_view_state(data.get("view"))
            self.current_file = path
            self.project_dir = os.path.dirname(path)
            basename = os.path.basename(path)
            self.breadcrumb = data.get("breadcrumb") or [
                {"name": os.path.splitext(basename)[0], "file": basename}
            ]
            self._set_base_title(f"OpenNote \u2014 {basename}")
            self.statusBar().showMessage(f"Opened: {path}", 4000)
            self._update_breadcrumb_bar()
            # Liczymy snapshot JSON planszy raz, zamiast dwa razy pod
            # rząd (_update_saved_snapshot i _reset_undo_history
            # osobno serializowały cały board zaraz po wczytaniu) -
            # dla dużych boardów ze zdjęciami to niepotrzebnie
            # podwajało koszt (patrz też _b64_cache w ImageItem).
            snapshot = self._current_snapshot()
            self._update_saved_snapshot(snapshot)
            self._reset_undo_history(snapshot)
            self._add_recent_file(path)
        except Exception as e:
            QMessageBox.critical(self, error_title, str(e))

    # -- breadcrumb bar (nested-boards navigation) -----------------------
    def _update_breadcrumb_bar(self):
        layout = self.breadcrumb_layout
        while layout.count() > 0:
            child = layout.takeAt(0)
            w = child.widget()
            if w is not None:
                w.deleteLater()

        project_dir = os.path.dirname(self.current_file) if self.current_file else None
        for i, seg in enumerate(self.breadcrumb):
            if i > 0:
                sep = QLabel(" \u203a ")
                sep.setStyleSheet("color:#555;")
                layout.addWidget(sep)
            is_last = i == len(self.breadcrumb) - 1
            name = seg.get("name") or "Untitled"
            btn = QToolButton()
            btn.setText(name)
            btn.setAutoRaise(True)
            btn.setFocusPolicy(Qt.NoFocus)
            if is_last:
                btn.setEnabled(False)
                btn.setStyleSheet("QToolButton { color:#eee; font-weight:600; }")
            else:
                target_file = seg.get("file")
                target_path = os.path.join(project_dir, target_file) if (project_dir and target_file) else None
                enabled = bool(target_path and os.path.exists(target_path))
                btn.setEnabled(enabled)
                btn.setStyleSheet(
                    "QToolButton { color:#8ab4ff; } QToolButton:hover { text-decoration:underline; }"
                    if enabled else "QToolButton { color:#666; }"
                )
                if enabled:
                    btn.clicked.connect(lambda checked=False, p=target_path: self.navigate_to_file(p))
            layout.addWidget(btn)
        layout.addStretch(1)


# --------------------------------------------------------------------------
# Theme
# --------------------------------------------------------------------------

def apply_dark_theme(app):
    app.setStyle("Fusion")
    palette = QPalette()
    palette.setColor(QPalette.Window, QColor(30, 30, 30))
    palette.setColor(QPalette.WindowText, Qt.white)
    palette.setColor(QPalette.Base, QColor(24, 24, 24))
    palette.setColor(QPalette.AlternateBase, QColor(45, 45, 45))
    palette.setColor(QPalette.ToolTipBase, Qt.white)
    palette.setColor(QPalette.ToolTipText, Qt.white)
    palette.setColor(QPalette.Text, Qt.white)
    palette.setColor(QPalette.Button, QColor(45, 45, 45))
    palette.setColor(QPalette.ButtonText, Qt.white)
    palette.setColor(QPalette.Highlight, QColor(76, 139, 245))
    palette.setColor(QPalette.HighlightedText, Qt.black)
    app.setPalette(palette)


def main():
    # Use a single, explicit high-DPI rounding policy *before* the
    # QApplication is created. Qt6/PySide6 already enables per-monitor
    # DPI awareness by default on Windows (that's the informational
    # "DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2" message you see in the
    # console - it is not an error). Leaving the rounding policy on its
    # default ("Round") is what usually causes toolbars/menus to be
    # mis-measured and rendered in the wrong place on fractional scale
    # factors (125%, 150%, etc). PassThrough fixes that mismatch.
    QGuiApplication.setHighDpiScaleFactorRoundingPolicy(
        Qt.HighDpiScaleFactorRoundingPolicy.PassThrough
    )

    app = QApplication(sys.argv)
    app.setApplicationName("OpenNote")
    apply_dark_theme(app)
    win = MainWindow()

    # Explicitly place the window on the primary screen instead of relying
    # on the OS default placement, which is what produced the odd
    # off-screen / off-center window position - then open maximized
    # (fills the screen, but keeps window chrome/taskbar, unlike true
    # borderless fullscreen) so the app starts ready to use at full size.
    screen = app.primaryScreen()
    if screen is not None:
        avail = screen.availableGeometry()
        win.resize(min(1440, avail.width() - 80), min(900, avail.height() - 80))
        win.move(avail.center() - win.rect().center())

    win.showMaximized()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
