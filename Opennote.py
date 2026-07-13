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
import math
import json
import base64
import atexit
import tempfile
import uuid
import time

from PySide6.QtCore import (
    Qt, QRectF, QPointF, QPoint, QSize, QSizeF, QByteArray, QBuffer, QIODevice, QUrl,
)
from PySide6.QtGui import (
    QColor, QPen, QPainter, QPainterPath, QPixmap, QImage, QFont, QFontMetrics,
    QMovie, QPalette, QKeySequence, QAction, QGuiApplication,
    QIcon, QActionGroup, QTextCursor,
)
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QGraphicsView, QGraphicsScene, QGraphicsObject,
    QGraphicsItem, QGraphicsTextItem, QGraphicsPathItem, QGraphicsProxyWidget,
    QToolBar, QFileDialog, QColorDialog, QMessageBox, QSlider, QComboBox,
    QPushButton, QLabel, QWidget, QVBoxLayout, QHBoxLayout, QMenu, QToolButton,
    QFontComboBox, QInputDialog, QCompleter, QCheckBox,
    QDialog, QDialogButtonBox, QFormLayout, QSpinBox, QGridLayout, QLineEdit,
)

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

IMAGE_EXTS = {".png", ".jpg", ".jpeg", ".bmp", ".webp"}
GIF_EXTS = {".gif"}
VIDEO_EXTS = {".mp4", ".mov", ".avi", ".webm", ".mkv"}

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
    cell at once, the same way this restyles a whole Text Note)."""
    targets = item.font_targets(editing_item) if hasattr(item, "font_targets") else [item.text_item]
    for t in targets:
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
    if isinstance(item, TextNoteItem):
        item._on_text_changed()
        item.update()


def _representative_font(item, editing_item=None):
    """The font shown in the toolbar (combo/B/I/U/size) for the current
    selection - the font of whichever single cell is being edited, or of
    the first cell/text item otherwise."""
    if hasattr(item, "font_targets"):
        targets = item.font_targets(editing_item)
        return targets[0].font() if targets else QFont("Segoe UI", 10)
    return item.text_item.font()


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
        if self._losing_focus_to_font_combo():
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
        if event.key() in (Qt.Key_Return, Qt.Key_Enter):
            parent = self.parentItem()
            mode = getattr(parent, "list_mode", None)
            if mode:
                prefix = BULLET_CHAR if mode == "bullet" else CHECK_UNCHECKED
                cursor = self.textCursor()
                block_text = cursor.block().text()
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

    def mouseMoveEvent(self, event):
        if self.textInteractionFlags() == Qt.NoTextInteraction:
            event.ignore()
            return
        super().mouseMoveEvent(event)

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
        )
        self.setAcceptHoverEvents(True)
        self.min_w, self.min_h = 80, 60
        self._resizing = False
        self._resize_start = QPointF()
        self._start_geom = (self._w, self._h)
        # Board card this item is currently hovering over while being
        # dragged, if any - tracked so we can show/clear the insertion
        # preview line on the target card as the drag moves, instead of
        # only deciding a drop position at release time.
        self._hover_board = None

    # -- geometry -----------------------------------------------------
    def boundingRect(self):
        return QRectF(-2, -2, self._w + 4, self._h + 4)

    def rect(self):
        return QRectF(0, 0, self._w, self._h)

    def set_size(self, w, h):
        self.prepareGeometryChange()
        self._w = max(self.min_w, w)
        self._h = max(self.min_h, h)
        self.on_resized()
        self.update()

    def on_resized(self):
        pass

    def set_color(self, color):
        self.color = color.name() if isinstance(color, QColor) else color
        self.update()

    def _frame_pen(self, default="#000000"):
        """Border pen used by image/gif/video items: blue while selected,
        otherwise the user's custom color if they set one, else `default`."""
        if self.isSelected():
            return QPen(QColor("#4c8bf5"), 2)
        return QPen(QColor(self.color) if self.color else QColor(default), 1)

    def handle_rect(self):
        return QRectF(self._w - HANDLE_SIZE, self._h - HANDLE_SIZE, HANDLE_SIZE, HANDLE_SIZE)

    def paint_handle(self, painter):
        if self.isSelected():
            painter.setBrush(QColor("#4c8bf5"))
            painter.setPen(QPen(QColor("#ffffff"), 1))
            painter.drawRect(self.handle_rect())

    # -- mouse: resize / drag-drop-onto-board notification ------------
    def mousePressEvent(self, event):
        if self.isSelected() and self.handle_rect().contains(event.pos()):
            self._resizing = True
            self._resize_start = event.scenePos()
            self._start_geom = (self._w, self._h)
            event.accept()
            return
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if self._resizing:
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
        super().mouseMoveEvent(event)
        self._update_board_hover_preview()

    def _update_board_hover_preview(self):
        """While this item is being dragged around the canvas (not
        resized), show a live insertion-line preview on whichever board
        card it is currently over, so the user can see exactly where the
        component will land instead of it always jumping to the end of
        the card's contents on drop."""
        if isinstance(self, BoardCardItem):
            return
        scene = self.scene()
        if scene is None:
            return
        try:
            center = self.mapToScene(self.rect().center())
        except Exception:
            return
        target = None
        for other in scene.items(center):
            if isinstance(other, BoardCardItem) and other is not self:
                target = other
                break
        prev = self._hover_board
        if prev is not None and prev is not target:
            prev.clear_insert_preview()
        if target is not None:
            target.show_insert_preview(target.mapFromScene(center).y())
        self._hover_board = target

    def mouseReleaseEvent(self, event):
        was_resizing = self._resizing
        if self._resizing:
            self._resizing = False
            event.accept()
        else:
            super().mouseReleaseEvent(event)
        if self._hover_board is not None:
            self._hover_board.clear_insert_preview()
            self._hover_board = None
        scene = self.scene()
        if scene is not None and not was_resizing and hasattr(scene, "item_drag_released"):
            scene.item_drag_released(self)

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

    def contextMenuEvent(self, event):
        menu = QMenu()
        self._build_context_menu(menu)
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
        }

    def to_html(self):
        raise NotImplementedError


# --------------------------------------------------------------------------
# Text note
# --------------------------------------------------------------------------

class TextNoteItem(BaseComponentItem):
    TYPE_NAME = "text"
    DEFAULT_COLOR = "#1e1e1e"
    DEFAULT_TEXT_COLOR = "#e8e8e8"

    TITLE_H = 28

    def __init__(self, x=0, y=0, w=220, h=140, text="New note", color=None, item_id=None,
                 font_family=None, font_size=None, bold=False, italic=False, underline=False,
                 link_url=None, text_color=None, title="Title", show_title=False, title_font=None):
        super().__init__(x, y, w, h, item_id)
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
        menu.addSeparator()
        self._bullet_menu_action = menu.addAction("Toggle Bullet List")
        self._check_menu_action = menu.addAction("Toggle Checklist")
        menu.addSeparator()

    def _handle_context_action(self, action):
        if action == self._title_menu_action:
            self._toggle_show_title()
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
        return d

    def to_html(self):
        text = (
            self.text_item.toPlainText()
            .replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
            .replace("\n", "<br>")
        )
        f = self.text_item.font()
        text_color = self.text_item.defaultTextColor().name()
        # pointSizeF() is a point size, not a pixel size - tagging it "pt"
        # (rather than "px") keeps the exported size in sync with the app,
        # the same fix already applied to the Arrow label's font-size.
        style_bits = [
            f"font-family:'{f.family()}',sans-serif",
            f"font-size:{f.pointSizeF():.1f}pt",
            f"color:{text_color}",
        ]
        if f.bold():
            style_bits.append("font-weight:bold")
        if f.italic():
            style_bits.append("font-style:italic")
        if f.underline():
            style_bits.append("text-decoration:underline")
        text_style = ";".join(style_bits)
        if self.link_url:
            safe_url = self.link_url.replace('"', "&quot;")
            link_style = text_style if f.underline() else f"{text_style};text-decoration:underline"
            text = f'<a href="{safe_url}" target="_blank" rel="noopener noreferrer" style="{link_style}">{text}</a>'
        else:
            text = f'<span style="{text_style}">{text}</span>'
        bg_css = color_to_css(self.color)
        title_html = ""
        if self.show_title:
            title_text = (
                self.title_item.toPlainText()
                .replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
                .replace("\n", "<br>")
            )
            tf = self.title_item.font()
            title_color = color_to_css(self.title_item.defaultTextColor().name())
            title_bits = [
                f"font-family:'{tf.family()}',sans-serif",
                f"font-size:{tf.pointSizeF():.1f}pt",
                "margin-bottom:4px",
                f"color:{title_color}",
            ]
            title_bits.append("font-weight:bold" if tf.bold() else "font-weight:normal")
            if tf.italic():
                title_bits.append("font-style:italic")
            if tf.underline():
                title_bits.append("text-decoration:underline")
            title_html = f'<div style="{";".join(title_bits)}">{title_text}</div>'
        return (
            f'<div class="comp text-note" style="left:{self.pos().x()}px;top:{self.pos().y()}px;'
            f'width:{self._w}px;height:{self._h}px;background:{bg_css};'
            f'opacity:{self.opacity():.2f}">{title_html}{text}</div>'
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
                 link_url=None):
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
        return d

    def to_html(self):
        text = (
            self.text_item.toPlainText()
            .replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
            .replace("\n", "<br>")
        )
        f = self.text_item.font()
        text_color = QColor(self.color).name()
        style_bits = [
            f"font-family:'{f.family()}',sans-serif",
            f"font-size:{f.pointSizeF():.1f}pt",
            f"color:{text_color}",
        ]
        if f.bold():
            style_bits.append("font-weight:bold")
        if f.italic():
            style_bits.append("font-style:italic")
        if f.underline():
            style_bits.append("text-decoration:underline")
        text_style = ";".join(style_bits)
        if self.link_url:
            safe_url = self.link_url.replace('"', "&quot;")
            link_style = text_style if f.underline() else f"{text_style};text-decoration:underline"
            text = f'<a href="{safe_url}" target="_blank" rel="noopener noreferrer" style="{link_style}">{text}</a>'
        else:
            text = f'<span style="{text_style}">{text}</span>'
        return (
            f'<div class="comp plain-text-note" style="left:{self.pos().x()}px;top:{self.pos().y()}px;'
            f'width:{self._w}px;height:{self._h}px;'
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
                          title_font=None, desc_font=None, title_color=None, desc_color=None):
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

        self.description_item = EditableTextItem(self)
        self.description_item.setDefaultTextColor(QColor(desc_color) if desc_color else QColor("#aaaaaa"))
        self.description_item.setFont(
            _font_from_dict(desc_font, base_family="Segoe UI", base_size=9.0, base_bold=False)
            if desc_font else QFont("Segoe UI", 9)
        )
        self.description_item.setPlainText(description)
        self.description_item.setTextInteractionFlags(Qt.NoTextInteraction)
        self.description_item.document().setDocumentMargin(4)

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
        painter.setBrush(QColor("#1e1e1e"))
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
        title = self._escape_html(self.title_item.toPlainText()) if self.show_title else ""
        desc = self._escape_html(self.description_item.toPlainText()) if self.show_description else ""
        title_style = self._font_style_css(self.title_item.font(), self.title_item.defaultTextColor().name())
        desc_style = self._font_style_css(self.description_item.font(), self.description_item.defaultTextColor().name())
        return (
            f'<div class="media-title" style="{title_style}">{title}</div>' if title else "",
            f'<div class="media-desc" style="{desc_style}">{desc}</div>' if desc else "",
        )

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
        return False


class ImageItem(MediaCardMixin, BaseComponentItem):
    TYPE_NAME = "image"

    def __init__(self, x=0, y=0, w=240, h=180, pixmap=None, b64=None, item_id=None,
                 title="", description="", show_title=True, show_description=True,
                 title_font=None, desc_font=None, title_color=None, desc_color=None):
        super().__init__(x, y, w, h, item_id)
        self.pixmap_orig = pixmap if pixmap is not None else base64_to_pixmap(b64)
        self.min_w, self.min_h = 120, 140
        self.setAcceptDrops(True)
        self._init_title_desc(title, description, show_title, show_description,
                               title_font=title_font, desc_font=desc_font,
                               title_color=title_color, desc_color=desc_color)

    def set_pixmap(self, pixmap):
        self.pixmap_orig = pixmap
        self.update()

    def on_resized(self):
        self._layout_title_desc()

    def mouseDoubleClickEvent(self, event):
        if self._title_desc_double_click(event):
            event.accept()
            return
        super().mouseDoubleClickEvent(event)

    def _build_context_menu(self, menu):
        self._build_media_context_menu(menu)

    def _handle_context_action(self, action):
        self._handle_media_context_action(action)

    def paint(self, painter, option, widget=None):
        painter.setRenderHint(QPainter.SmoothPixmapTransform)
        rect = self._media_rect()
        painter.setBrush(QColor("#111111"))
        painter.setPen(Qt.NoPen)
        painter.drawRect(rect)
        if not self.pixmap_orig.isNull():
            scaled = self.pixmap_orig.scaled(
                rect.size().toSize(), Qt.KeepAspectRatio, Qt.SmoothTransformation
            )
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
        d["data"] = pixmap_to_base64(self.pixmap_orig)
        return self._title_desc_serialize(d)

    def to_html(self):
        b64 = pixmap_to_base64(self.pixmap_orig)
        title_html, desc_html = self._title_desc_html()
        return (
            f'<div class="comp image-note" style="left:{self.pos().x()}px;top:{self.pos().y()}px;'
            f'width:{self._w}px;height:{self._h}px;">{title_html}'
            f'<img src="data:image/png;base64,{b64}" />{desc_html}</div>'
        )


# --------------------------------------------------------------------------
# GIF (animated)
# --------------------------------------------------------------------------

class GifItem(MediaCardMixin, BaseComponentItem):
    TYPE_NAME = "gif"

    def __init__(self, x=0, y=0, w=240, h=180, gif_bytes=None, b64=None, item_id=None,
                 title="", description="", show_title=True, show_description=True,
                 title_font=None, desc_font=None, title_color=None, desc_color=None):
        super().__init__(x, y, w, h, item_id)
        if gif_bytes is not None:
            self.gif_bytes = gif_bytes
        elif b64:
            self.gif_bytes = base64.b64decode(b64)
        else:
            self.gif_bytes = b""
        self.buffer = None
        self.movie = None
        self._current_pixmap = QPixmap()
        self.min_w, self.min_h = 120, 140
        self.setAcceptDrops(True)
        self._init_title_desc(title, description, show_title, show_description,
                               title_font=title_font, desc_font=desc_font,
                               title_color=title_color, desc_color=desc_color)
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
            self.update()

    def set_gif_bytes(self, data):
        if self.movie:
            self.movie.stop()
        self.gif_bytes = data
        self._setup_movie()

    def on_resized(self):
        self._layout_title_desc()

    def mouseDoubleClickEvent(self, event):
        if self._title_desc_double_click(event):
            event.accept()
            return
        super().mouseDoubleClickEvent(event)

    def _build_context_menu(self, menu):
        self._build_media_context_menu(menu)

    def _handle_context_action(self, action):
        self._handle_media_context_action(action)

    def paint(self, painter, option, widget=None):
        rect = self._media_rect()
        painter.setBrush(QColor("#111111"))
        painter.setPen(Qt.NoPen)
        painter.drawRect(rect)
        if not self._current_pixmap.isNull():
            scaled = self._current_pixmap.scaled(
                rect.size().toSize(), Qt.KeepAspectRatio, Qt.SmoothTransformation
            )
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
        return self._title_desc_serialize(d)

    def to_html(self):
        b64 = base64.b64encode(self.gif_bytes).decode("ascii") if self.gif_bytes else ""
        title_html, desc_html = self._title_desc_html()
        return (
            f'<div class="comp gif-note" style="left:{self.pos().x()}px;top:{self.pos().y()}px;'
            f'width:{self._w}px;height:{self._h}px;">{title_html}'
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
            self.player = QMediaPlayer()
            self.audio = QAudioOutput()
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

        self.resize(self._w, self._h)
        if video_bytes:
            self.set_video_bytes(video_bytes)

    def boundingRect(self):
        return QRectF(0, 0, self._w, self._h)

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


class VideoItem(MediaCardMixin, BaseComponentItem):
    TYPE_NAME = "video"
    DRAG_STRIP_H = 16

    def __init__(self, x=0, y=0, w=320, h=220, video_bytes=None, b64=None, item_id=None,
                 title="", description="", show_title=True, show_description=True,
                 title_font=None, desc_font=None, title_color=None, desc_color=None):
        super().__init__(x, y, w, h, item_id)
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
                               title_color=title_color, desc_color=desc_color)
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
        self._build_media_context_menu(menu)

    def _handle_context_action(self, action):
        self._handle_media_context_action(action)

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
        return self._title_desc_serialize(d)

    def to_html(self):
        b64 = base64.b64encode(self.video_bytes).decode("ascii") if self.video_bytes else ""
        title_html, desc_html = self._title_desc_html()
        return (
            f'<div class="comp video-note" style="left:{self.pos().x()}px;top:{self.pos().y()}px;'
            f'width:{self._w}px;height:{self._h}px;">{title_html}'
            f'<video controls src="data:video/mp4;base64,{b64}"></video>{desc_html}</div>'
        )


# --------------------------------------------------------------------------
# Freehand drawing
# --------------------------------------------------------------------------

class DrawingItem(BaseComponentItem):
    TYPE_NAME = "drawing"

    def __init__(self, x=0, y=0, w=100, h=100, strokes=None, item_id=None):
        super().__init__(x, y, w, h, item_id)
        self.strokes = strokes or []
        self.min_w, self.min_h = 20, 20

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
            f'<div class="comp drawing-note" style="left:{self.pos().x()}px;top:{self.pos().y()}px;'
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
                 label="", show_label=False, label_font=None, label_color=None):
        super().__init__(x, y, max(1.0, w), max(1.0, h), item_id)
        self.color = color or self.DEFAULT_COLOR
        self.stroke_width = stroke_width
        self.style = style if style in self.STYLES else "single"
        self.line_style = line_style if line_style in self.LINE_STYLES else "solid"
        self.min_w, self.min_h = 1, 1
        self.p1 = QPointF(*p1) if p1 else QPointF(self.PAD, self._h - self.PAD)
        self.p2 = QPointF(*p2) if p2 else QPointF(self._w - self.PAD, self.PAD)
        self._drag_endpoint = None  # 1, 2, or None while dragging an end

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
        return rect

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
            scene_pt = event.scenePos()
            if event.modifiers() & Qt.ControlModifier:
                # Rotate around the endpoint that is *not* being dragged,
                # snapping every 45 degrees.
                pivot = self.mapToScene(self.p2 if self._drag_endpoint == 1 else self.p1)
                scene_pt = self._snap_to_angle(pivot, scene_pt)
            if self._drag_endpoint == 1:
                self._sync_geometry(scene_pt, self.mapToScene(self.p2))
            else:
                self._sync_geometry(self.mapToScene(self.p1), scene_pt)
            event.accept()
            return
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        if self._drag_endpoint is not None:
            self._drag_endpoint = None
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
        self.setPos(x0, y0)
        self._w = max(1.0, x1 - x0)
        self._h = max(1.0, y1 - y0)
        self.p1 = QPointF(p1_scene.x() - x0, p1_scene.y() - y0)
        self.p2 = QPointF(p2_scene.x() - x0, p2_scene.y() - y0)
        self._layout_label()
        self.update()

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

        dx, dy = self.p2.x() - self.p1.x(), self.p2.y() - self.p1.y()
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
        line_p1, line_p2 = self.p1, self.p2
        if self.style == "double":
            b = min(back, length * 0.45)
            line_p1 = QPointF(self.p1.x() + ux * b, self.p1.y() + uy * b)
            line_p2 = QPointF(self.p2.x() - ux * b, self.p2.y() - uy * b)
        elif self.style == "single":
            b = min(back, length * 0.9)
            line_p2 = QPointF(self.p2.x() - ux * b, self.p2.y() - uy * b)
        painter.drawLine(line_p1, line_p2)

        painter.setBrush(col)
        painter.setPen(Qt.NoPen)
        if self.style in ("single", "double"):
            painter.drawPath(self._arrow_head_path(self.p2, ux, uy))
        if self.style == "double":
            painter.drawPath(self._arrow_head_path(self.p1, -ux, -uy))

        if self.isSelected():
            painter.setPen(QPen(QColor("#4c8bf5"), 1.5))
            painter.setBrush(QColor("#4c8bf5"))
            painter.drawEllipse(self.p1, self.ENDPOINT_R, self.ENDPOINT_R)
            painter.drawEllipse(self.p2, self.ENDPOINT_R, self.ENDPOINT_R)

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
        return d

    def to_html(self):
        css_color = color_to_css(self.color)
        dx, dy = self.p2.x() - self.p1.x(), self.p2.y() - self.p1.y()
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
        line_p1x, line_p1y = self.p1.x(), self.p1.y()
        line_p2x, line_p2y = self.p2.x(), self.p2.y()
        if self.style == "double":
            b = min(back, length * 0.45)
            line_p1x, line_p1y = self.p1.x() + ux * b, self.p1.y() + uy * b
            line_p2x, line_p2y = self.p2.x() - ux * b, self.p2.y() - uy * b
        elif self.style == "single":
            b = min(back, length * 0.9)
            line_p2x, line_p2y = self.p2.x() - ux * b, self.p2.y() - uy * b

        heads = []
        if self.style in ("single", "double"):
            heads.append(f'<polygon points="{head_polygon(self.p2.x(), self.p2.y(), ux, uy)}" fill="{css_color}"/>')
        if self.style == "double":
            heads.append(f'<polygon points="{head_polygon(self.p1.x(), self.p1.y(), -ux, -uy)}" fill="{css_color}"/>')
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
            text = (
                self.label_item.toPlainText()
                .replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
                .replace("\n", "<br>")
            )
            mid_x = (self.p1.x() + self.p2.x()) / 2.0
            mid_y = (self.p1.y() + self.p2.y()) / 2.0
            lf = self.label_item.font()
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
            f'<div class="comp arrow-note" style="left:{self.pos().x()}px;'
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
    ]

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
        self._swatches[name].setStyleSheet(
            f"background-color:{col.name()}; border:1px solid #888;"
        )

    def _pick(self, name):
        chosen = QColorDialog.getColor(self._colors[name], self, "Pick color")
        if chosen.isValid():
            self._colors[name] = chosen
            self._refresh_swatch(name)

    def apply_to_table(self):
        self.table_item.set_grid_size(self.rows_spin.value(), self.cols_spin.value())
        self.table_item.set_colors(**{name: col.name() for name, col in self._colors.items()})


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

    CELL_PAD = 6

    def __init__(self, x=0, y=0, w=360, h=200, rows=3, cols=3, item_id=None,
                 data=None, headers=None, header_bg=None, header_text_color=None,
                 text_color=None, even_row_bg=None, odd_row_bg=None,
                 even_row_text_color=None, odd_row_text_color=None,
                 header_fonts=None, data_fonts=None):
        super().__init__(x, y, w, h, item_id)
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
        self._build_grid_items(init_headers, init_data, init_header_fonts, init_data_fonts)
        self._update_min_size()

    # -- grid content (child EditableTextItems are the source of truth) --
    def _make_cell_item(self, text, color, bold=False, font_info=None):
        it = EditableTextItem(self)
        it.setTextInteractionFlags(Qt.NoTextInteraction)
        f = _font_from_dict(font_info, base_bold=bold) if font_info else QFont("Segoe UI", 10)
        if not font_info:
            f.setBold(bold)
        it.setFont(f)
        it.setDefaultTextColor(QColor(color))
        it.setPlainText(text)
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

    def _build_grid_items(self, headers_text, data_text, header_fonts=None, data_fonts=None):
        self._grid_ready = False
        header_fonts = header_fonts or [None] * self.cols
        self._header_items = [
            self._make_cell_item(headers_text[c], self.header_text_color, bold=True,
                                  font_info=header_fonts[c] if c < len(header_fonts) else None)
            for c in range(self.cols)
        ]
        self._cell_items = []
        data_fonts = data_fonts or [[None] * self.cols for _ in range(self.rows)]
        for r in range(self.rows):
            is_even = (r + 1) % 2 == 0
            row_color = self.even_row_text_color if is_even else self.odd_row_text_color
            row_fonts = data_fonts[r] if r < len(data_fonts) else [None] * self.cols
            self._cell_items.append(
                [self._make_cell_item(data_text[r][c], row_color,
                                       font_info=row_fonts[c] if c < len(row_fonts) else None)
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
        self.prepareGeometryChange()
        self.rows = max(1, int(rows))
        self.cols = max(1, int(cols))
        new_headers = (old_headers + [""] * self.cols)[:self.cols]
        new_header_fonts = (old_header_fonts + [None] * self.cols)[:self.cols]
        new_data = []
        new_data_fonts = []
        for r in range(self.rows):
            row = old_data[r] if r < len(old_data) else []
            row = (list(row) + [""] * self.cols)[:self.cols]
            new_data.append(row)
            row_fonts = old_data_fonts[r] if r < len(old_data_fonts) else []
            row_fonts = (list(row_fonts) + [None] * self.cols)[:self.cols]
            new_data_fonts.append(row_fonts)
        self._clear_grid_items()
        self._build_grid_items(new_headers, new_data, new_header_fonts, new_data_fonts)
        self._update_min_size()
        self.update()

    def set_colors(self, header_bg=None, header_text_color=None, text_color=None,
                    even_row_bg=None, odd_row_bg=None, even_row_text_color=None,
                    odd_row_text_color=None):
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

        # Grid lines
        painter.setBrush(Qt.NoBrush)
        painter.setPen(QPen(QColor(0, 0, 0, 90), 1))
        for c in range(1, self.cols):
            x = rect.x() + c * col_w
            painter.drawLine(QPointF(x, rect.y()), QPointF(x, rect.y() + rect.height()))
        for yb in boundaries:
            painter.drawLine(QPointF(rect.x(), rect.y() + yb), QPointF(rect.x() + rect.width(), rect.y() + yb))

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
        d["header_bg"] = self.header_bg
        d["header_text_color"] = self.header_text_color
        d["text_color"] = self.text_color
        d["even_row_bg"] = self.even_row_bg
        d["odd_row_bg"] = self.odd_row_bg
        d["even_row_text_color"] = self.even_row_text_color
        d["odd_row_text_color"] = self.odd_row_text_color
        return d

    def to_html(self):
        def esc(s):
            return (
                (s or "")
                .replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
                .replace("\n", "<br>")
            )

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

        headers = self._current_headers()
        data = self._current_data()
        header_fonts = self._current_header_fonts()
        data_fonts = self._current_data_fonts()
        header_cells = "".join(
            f'<th style="text-align:left;padding:6px;background:{color_to_css(self.header_bg)};'
            f'color:{color_to_css(self.header_text_color)};'
            f'{";".join(font_style_bits(header_fonts[c]))}">{esc(h)}</th>'
            for c, h in enumerate(headers)
        )
        body_rows = []
        for r in range(self.rows):
            is_even = (r + 1) % 2 == 0
            row_bg = self.even_row_bg if is_even else self.odd_row_bg
            row_text_color = self.even_row_text_color if is_even else self.odd_row_text_color
            cells = "".join(
                f'<td style="padding:6px;background:{color_to_css(row_bg)};'
                f'color:{color_to_css(row_text_color)};'
                f'{";".join(font_style_bits(data_fonts[r][c]))}">{esc(data[r][c])}</td>'
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
            f'<div class="comp table-note" style="left:{self.pos().x()}px;top:{self.pos().y()}px;'
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


class BoardCardItem(BaseComponentItem):
    TYPE_NAME = "board"
    DEFAULT_COLOR = "#2b2b2b"
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

    def __init__(self, x=0, y=0, w=280, h=320, title="New Board", subitems=None, item_id=None):
        super().__init__(x, y, w, h, item_id)
        self.subitems = subitems or []
        self.min_w, self.min_h = 160, 120
        self.setAcceptDrops(True)
        self.title_item = EditableTextItem(self)
        self.title_item.setPos(10, 6)
        self.title_item.setFont(QFont("Segoe UI", 12, QFont.Bold))
        self.title_item.setDefaultTextColor(QColor("#ffffff"))
        self.title_item.setPlainText(title)
        self.title_item.setTextInteractionFlags(Qt.NoTextInteraction)
        self.title_item.setTextWidth(max(10, w - 20))

        # -- subitem drag-out / reorder state ---------------------------
        # Filled in during paint() so hit-testing always matches what is
        # currently on screen.
        self._subitem_rects = []      # list of (index, QRectF-in-item-coords)
        self._drag_sub_index = None   # index currently being dragged, or None
        self._drag_sub_moved = False  # did the mouse actually move past a threshold
        self._drag_sub_start_pos = QPointF()
        self._drag_sub_will_detach = False
        self._drag_ghost = None       # floating SubitemDragGhost while dragging

        # -- in-place text-subitem editing state -------------------------
        self._sub_edit_item = None    # the _SubitemTextEdit overlay, while editing
        self._sub_edit_index = None   # index of the subitem being edited
        self._subitem_font = QFont()  # font used for text subitems, captured in paint()

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

    def on_resized(self):
        self.title_item.setTextWidth(max(10, self._w - 20))
        self.update()

    def mouseDoubleClickEvent(self, event):
        if event.pos().y() < 36:
            self.title_item.setTextInteractionFlags(Qt.TextEditorInteraction)
            self.title_item.setFocus()
        else:
            idx = self._subitem_index_at(event.pos())
            if idx is not None and self.subitems[idx].get("kind") == "text":
                self._begin_edit_subitem(idx)
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
        edit = _SubitemTextEdit(self, on_finish=self._end_edit_subitem)
        edit.setPos(rect.x(), rect.y())
        edit.setTextWidth(max(10, rect.width()))
        edit.setDefaultTextColor(QColor("#dddddd"))
        edit.setFont(self._subitem_font)
        edit.setPlainText(self.subitems[idx].get("text", ""))
        edit.document().contentsChanged.connect(lambda: self._sync_subitem_text(idx))
        edit.setZValue(10)
        self._sub_edit_item = edit
        self._sub_edit_index = idx
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
        self._autogrow_to_fit()
        self.update()

    def _end_edit_subitem(self):
        edit = self._sub_edit_item
        if edit is None:
            return
        idx = self._sub_edit_index
        if idx is not None and idx < len(self.subitems):
            self.subitems[idx]["text"] = edit.toPlainText()
        self._sub_edit_item = None
        self._sub_edit_index = None
        edit.setParentItem(None)
        if edit.scene() is not None:
            edit.scene().removeItem(edit)
        self.update()

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

    def _sub_media_chrome(self, item):
        """For an image/gif/video subitem, decide whether its title/desc
        bars should be drawn (on AND actually has text) and how tall each
        one is - shared by paint() and _estimate_content_height() so the
        two never disagree about how much vertical space a subitem needs."""
        show_title = bool(item.get("show_title", True)) and bool(item.get("title"))
        show_desc = bool(item.get("show_description", True)) and bool(item.get("description"))
        title_h = self.SUB_MEDIA_TITLE_H if show_title else 0
        desc_h = self.SUB_MEDIA_DESC_H if show_desc else 0
        return show_title, show_desc, title_h, desc_h

    def _paint_sub_media_title(self, painter, rect, text):
        painter.setPen(Qt.NoPen)
        painter.setBrush(QColor("#1e1e1e"))
        painter.drawRect(rect)
        painter.setPen(QColor("#ffffff"))
        painter.setFont(QFont("Segoe UI", 9, QFont.Bold))
        painter.drawText(rect.adjusted(6, 0, -6, 0), Qt.AlignVCenter | Qt.AlignLeft, text)

    def _paint_sub_media_desc(self, painter, rect, text):
        painter.setPen(Qt.NoPen)
        painter.setBrush(QColor("#1e1e1e"))
        painter.drawRect(rect)
        painter.setPen(QColor("#aaaaaa"))
        painter.setFont(QFont("Segoe UI", 8))
        painter.drawText(rect.adjusted(6, 0, -6, 0), Qt.AlignVCenter | Qt.AlignLeft, text)

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
        y = 42
        pad = 8
        avail_w = max(1, self._w - pad * 2)
        for item in self.subitems:
            kind = item.get("kind")
            if kind in ("image", "gif"):
                pm = base64_to_pixmap(item.get("data", ""))
                _, _, title_h, desc_h = self._sub_media_chrome(item)
                h = self._subitem_media_height(pm, avail_w, 10 ** 6) + title_h + desc_h
                y += h + self.MEDIA_GAP
            elif kind == "video":
                aspect = item.get("aspect") or (9 / 16)
                _, _, title_h, desc_h = self._sub_media_chrome(item)
                h = (self._subitem_media_height(None, avail_w, 10 ** 6, aspect=aspect)
                     + self.VIDEO_HANDLE_H + title_h + desc_h)
                y += h + self.MEDIA_GAP
            elif kind == "text":
                sub_font = QFont(item.get("font_family") or "Segoe UI", 10)
                sub_font.setBold(bool(item.get("bold")))
                sub_font.setItalic(bool(item.get("italic")))
                fm = QFontMetrics(sub_font)
                needed_h = fm.boundingRect(
                    QRectF(0, 0, avail_w, 10000).toRect(), Qt.TextWordWrap, item.get("text", "")
                ).height() + 4
                y += max(20, needed_h) + 8
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

    @staticmethod
    def _subitem_media_height(pm, avail_w, remaining_h, aspect=None, min_h=40, max_h=280):
        """Compute the reserved box height for an image/gif/video subitem
        so that its box matches the media's real aspect ratio (height/width)
        - this is what lets the media be drawn with KeepAspectRatio and
        exactly fill the box with no cropping and no empty bars, at any
        card width."""
        if aspect is None:
            if pm is not None and not pm.isNull() and pm.width() > 0:
                aspect = pm.height() / pm.width()
            else:
                aspect = 9 / 16
        h = avail_w * aspect
        return max(min_h, min(h, max_h, remaining_h))

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
        if event.button() == Qt.LeftButton and not (
            self.isSelected() and self.handle_rect().contains(event.pos())
        ):
            idx = self._subitem_index_at(event.pos())
            if idx is not None:
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
                sub = self.subitems.pop(idx)
                self._prune_video_proxies()
                self._prune_gif_movies()
                scene_pos = event.scenePos()
                new_item = subitem_to_component(sub, scene_pos.x() - 100, scene_pos.y() - 60)
                if new_item is not None and self.scene() is not None:
                    self.scene().addItem(new_item)
                    self.scene().clearSelection()
                    new_item.setSelected(True)
            self.update()
            event.accept()
            return
        super().mouseReleaseEvent(event)

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
        painter.drawRect(QRectF(0, 0, self._w, 36))
        painter.restore()

        y = 42
        pad = 8
        avail_w = self._w - pad * 2
        self._subitem_rects = []
        for idx, item in enumerate(self.subitems):
            remaining_h = self._h - y - pad
            if remaining_h < 18:
                break
            kind = item.get("kind")
            row_top = y
            if kind in ("image", "gif"):
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
                    pm = base64_to_pixmap(item.get("data", ""))
                # Size the reserved box itself to the media's own aspect
                # ratio (instead of a fixed 120px height) so drawing it
                # with KeepAspectRatio below fills the box exactly - no
                # cropping and no letterboxing, and it stays correct no
                # matter how the card gets resized afterwards.
                show_title, show_desc, title_h, desc_h = self._sub_media_chrome(item)
                media_h = self._subitem_media_height(pm, avail_w, remaining_h - title_h - desc_h)
                if show_title:
                    self._paint_sub_media_title(painter, QRectF(pad, y, avail_w, title_h), item.get("title", ""))
                    y += title_h
                r = QRectF(pad, y, avail_w, media_h)
                painter.setBrush(QColor("#111111"))
                painter.setPen(Qt.NoPen)
                painter.drawRect(r)
                if not pm.isNull():
                    scaled = pm.scaled(r.size().toSize(), Qt.KeepAspectRatio, Qt.SmoothTransformation)
                    px = r.x() + (r.width() - scaled.width()) / 2
                    py = r.y() + (r.height() - scaled.height()) / 2
                    painter.drawPixmap(int(px), int(py), scaled)
                y += media_h
                if show_desc:
                    self._paint_sub_media_desc(painter, QRectF(pad, y, avail_w, desc_h), item.get("description", ""))
                    y += desc_h
                y += self.MEDIA_GAP
                self._subitem_rects.append((idx, QRectF(pad, row_top, avail_w, y - row_top)))
            elif kind == "video":
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
                show_title, show_desc, title_h, desc_h = self._sub_media_chrome(item)
                if show_title:
                    self._paint_sub_media_title(painter, QRectF(pad, y, avail_w, title_h), item.get("title", ""))
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
                if show_desc:
                    self._paint_sub_media_desc(painter, QRectF(pad, y, avail_w, desc_h), item.get("description", ""))
                    y += desc_h
                y += self.MEDIA_GAP
                self._subitem_rects.append((idx, QRectF(pad, row_top, avail_w, y - row_top)))
            elif kind == "text":
                sub_font = QFont(item.get("font_family") or "Segoe UI", 10)
                sub_font.setBold(bool(item.get("bold")))
                sub_font.setItalic(bool(item.get("italic")))
                sub_font.setUnderline(bool(item.get("underline")))
                self._subitem_font = sub_font
                text = item.get("text", "")
                # A link gets the same blue tint (and underline, so it
                # reads as a link even without hovering) as it would as a
                # standalone Text component; otherwise fall back to the
                # subitem's own stored color if it has one (Text/plaintext
                # components carry their text color in "color"), else the
                # neutral default used before this had any color at all.
                if item.get("link_url"):
                    text_color = QColor("#5b9dd9")
                    sub_font.setUnderline(True)
                elif item.get("note_type") == "plaintext" and item.get("color"):
                    text_color = QColor(item.get("color"))
                elif item.get("note_type") == "text" and item.get("text_color"):
                    text_color = QColor(item.get("text_color"))
                elif not item.get("note_type") and item.get("color"):
                    # A subitem with no originating standalone component
                    # (e.g. colored via the Color button while editing it
                    # in place) - "color" is simply its text color here.
                    text_color = QColor(item.get("color"))
                else:
                    text_color = QColor("#dddddd")
                # Size the row to the text's actual wrapped height (instead
                # of a fixed 50px) so short text doesn't leave a stray gap
                # and long text doesn't spill past its row - previously
                # overflowing text just kept drawing past its row height
                # with nothing clipping it, so it visually bled underneath
                # whatever subitem (e.g. an image) got painted after it.
                fm = QFontMetrics(sub_font)
                needed_h = fm.boundingRect(
                    QRectF(0, 0, avail_w, 10000).toRect(), Qt.TextWordWrap, text
                ).height() + 4
                h = min(max(20, needed_h), remaining_h)
                r = QRectF(pad, y, avail_w, h)
                if idx != self._sub_edit_index:
                    painter.save()
                    painter.setClipRect(r)
                    painter.setFont(sub_font)
                    painter.setPen(text_color)
                    painter.drawText(r, Qt.TextWordWrap, text)
                    painter.restore()
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
                line_y = self._subitem_rects[-1][1].bottom() if self._subitem_rects else 42
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

    def serialize(self):
        d = super().serialize()
        d["title"] = self.title_item.toPlainText()
        d["subitems"] = self.subitems
        return d

    def to_html(self):
        rows = []
        for item in self.subitems:
            kind = item.get("kind")
            if kind in ("image", "gif", "video"):
                show_title = bool(item.get("show_title", True)) and bool(item.get("title"))
                show_desc = bool(item.get("show_description", True)) and bool(item.get("description"))
                t_html = (f'<div class="media-title">{MediaCardMixin._escape_html(item.get("title",""))}</div>'
                          if show_title else "")
                d_html = (f'<div class="media-desc">{MediaCardMixin._escape_html(item.get("description",""))}</div>'
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
                rows.append(f'<div class="{css_class}">{t_html}{media}{d_html}</div>')
            elif kind == "text":
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
                rows.append(f'<div class="sub-text">{t}</div>')
            elif kind == "checklist":
                lis = "".join(f'<li><input type="checkbox" disabled> {x}</li>' for x in item.get("items", []))
                rows.append(f'<ul class="sub-checklist">{lis}</ul>')
        title = (
            self.title_item.toPlainText()
            .replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
            .replace("\n", "<br>")
        )
        bg_css = color_to_css(self.color or self.DEFAULT_COLOR)
        return (
            f'<div class="comp board-card" style="left:{self.pos().x()}px;top:{self.pos().y()}px;'
            f'width:{self._w}px;height:{self._h}px;background:{bg_css};">'
            f'<div class="board-title">{title}</div>'
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

    def __init__(self, x=0, y=0, w=220, h=120, title="Board", target_file="", item_id=None,
                 thumb_mime=None, thumb_data=None):
        super().__init__(x, y, w, h, item_id)
        self.title = title or "Board"
        self.target_file = target_file or ""
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
                data = extract_scene_data(f.read())
            self._cached_count = len(data.get("items", [])) if data else 0
        except Exception:
            self._cached_count = None

    # -- painting -----------------------------------------------------
    def paint(self, painter, option, widget=None):
        self._refresh_count()
        rect = self.rect()
        painter.setRenderHint(QPainter.Antialiasing)
        bg = QColor(self.color or self.DEFAULT_COLOR)
        painter.setBrush(bg)
        painter.setPen(QPen(QColor("#4c8bf5"), 2) if self.isSelected() else QPen(QColor("#111111"), 1))
        painter.drawRoundedRect(rect, 10, 10)

        missing = self.target_file and self._project_dir() and not os.path.exists(self._target_path() or "")
        thumb = self._get_thumb_pixmap()

        if thumb is not None and not thumb.isNull():
            # Custom thumbnail: bleed it across the top of the card (clipped
            # to the card's own rounded outline) and push the title/subtitle
            # into the band below it.
            img_h = max(40.0, rect.height() * 0.58)
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
            title_rect = QRectF(12, img_h + 6, rect.width() - 24, rect.height() - img_h - 28)
            painter.drawText(title_rect, Qt.TextWordWrap | Qt.AlignLeft | Qt.AlignTop, self.title)

            sub_rect = QRectF(12, rect.height() - 20, rect.width() - 24, 16)
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
            title_rect = QRectF(12, 38, rect.width() - 24, rect.height() - 60)
            painter.drawText(title_rect, Qt.TextWordWrap | Qt.AlignLeft | Qt.AlignTop, self.title)

            sub_rect = QRectF(12, rect.height() - 24, rect.width() - 24, 18)

        painter.setFont(QFont("Segoe UI", 8))
        if missing:
            painter.setPen(QColor("#e08a80"))
            painter.drawText(sub_rect, Qt.AlignLeft | Qt.AlignVCenter, "Board file missing")
        else:
            painter.setPen(QColor("#9aa4b2"))
            count = self._cached_count
            label = f"{count} card{'s' if count != 1 else ''}" if count is not None else "Open board \u2192"
            painter.drawText(sub_rect, Qt.AlignLeft | Qt.AlignVCenter, label)

        self.paint_handle(painter)

    # -- navigation -----------------------------------------------------
    def mouseDoubleClickEvent(self, event):
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
        def _retarget(data):
            changed = False
            for it in data.get("items", []):
                if it.get("type") == "board_link" and it.get("target_file") == old_target_file:
                    it["target_file"] = new_target_file
                    if it.get("title") == old_name_no_ext:
                        it["title"] = safe_new_name
                    changed = True
            for seg in (data.get("breadcrumb") or []):
                if seg.get("file") == old_target_file:
                    seg["file"] = new_target_file
                    if seg.get("name") == old_name_no_ext:
                        seg["name"] = safe_new_name
                    changed = True
            return changed

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

        updated = 0
        for fname in os.listdir(proj):
            if not fname.lower().endswith(".html"):
                continue
            fpath = os.path.join(proj, fname)
            if os.path.normpath(fpath) == os.path.normpath(new_path):
                continue
            try:
                with open(fpath, "r", encoding="utf-8") as f:
                    data = extract_scene_data(f.read())
            except Exception:
                continue
            if data is None:
                continue
            if _retarget(data):
                try:
                    with open(fpath, "w", encoding="utf-8") as f:
                        f.write(build_html_document(data))
                    updated += 1
                except Exception:
                    pass

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
        return d

    def to_html(self):
        title = self.title.replace("&", "&amp;").replace("<", "&lt;")
        href = (self.target_file or "#").replace('"', "&quot;")
        thumb_html = ""
        if self.thumb_data:
            # Embedded exactly like any other image in the app - a plain
            # base64 `data:` URI, self-contained inside the exported HTML.
            thumb_html = f'<img class="board-link-thumb" src="data:{self.thumb_mime};base64,{self.thumb_data}"/>'
        return (
            f'<a class="comp board-link-card" href="{href}" '
            f'style="left:{self.pos().x()}px;top:{self.pos().y()}px;'
            f'width:{self._w}px;height:{self._h}px;">'
            f'{thumb_html}'
            f'<div class="board-link-title">{title}</div>'
            f'<div class="board-link-sub">Open board \u2192</div></a>'
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
        }
    if isinstance(item, (TextNoteItem, PlainTextItem)):
        f = item.text_item.font()
        return {
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
        }
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
        return {"kind": "image", "data": pixmap_to_base64(pm)}
    return None


def subitem_to_component(subitem, x, y):
    """Reverse of component_to_subitem: turn a board-card subitem back into
    a standalone, freely movable canvas component (used when a subitem is
    dragged out of its board card)."""
    kind = subitem.get("kind")
    if kind == "image":
        return ImageItem(x, y, b64=subitem.get("data"),
                          title=subitem.get("title", ""), description=subitem.get("description", ""),
                          show_title=subitem.get("show_title", True),
                          show_description=subitem.get("show_description", True),
                          title_font=subitem.get("title_font"), desc_font=subitem.get("description_font"),
                          title_color=subitem.get("title_color"), desc_color=subitem.get("description_color"))
    if kind == "gif":
        return GifItem(x, y, b64=subitem.get("data"),
                        title=subitem.get("title", ""), description=subitem.get("description", ""),
                        show_title=subitem.get("show_title", True),
                        show_description=subitem.get("show_description", True),
                        title_font=subitem.get("title_font"), desc_font=subitem.get("description_font"),
                        title_color=subitem.get("title_color"), desc_color=subitem.get("description_color"))
    if kind == "video":
        return VideoItem(x, y, b64=subitem.get("data"),
                          title=subitem.get("title", ""), description=subitem.get("description", ""),
                          show_title=subitem.get("show_title", True),
                          show_description=subitem.get("show_description", True),
                          title_font=subitem.get("title_font"), desc_font=subitem.get("description_font"),
                          title_color=subitem.get("title_color"), desc_color=subitem.get("description_color"))
    if kind == "text":
        cls = PlainTextItem if subitem.get("note_type") == "plaintext" else TextNoteItem
        kwargs = dict(
            text=subitem.get("text", ""),
            color=subitem.get("color"),
            font_family=subitem.get("font_family"),
            font_size=subitem.get("font_size"),
            bold=subitem.get("bold", False),
            italic=subitem.get("italic", False),
            underline=subitem.get("underline", False),
            link_url=subitem.get("link_url"),
        )
        if cls is TextNoteItem:
            kwargs["text_color"] = subitem.get("text_color")
        return cls(x, y, **kwargs)
    if kind == "checklist":
        # No standalone checklist component exists yet, so fall back to a
        # plain text note listing the checklist items.
        text = "\n".join(f"\u2022 {t}" for t in subitem.get("items", []))
        return TextNoteItem(x, y, text=text or "Checklist")
    return None


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
        )
    elif t == "plaintext":
        item = PlainTextItem(
            x, y, w, h, text=d.get("text", ""), color=d.get("color"), item_id=item_id,
            font_family=d.get("font_family"), font_size=d.get("font_size"),
            bold=d.get("bold", False), italic=d.get("italic", False),
            underline=d.get("underline", False), link_url=d.get("link_url"),
        )
    elif t == "image":
        item = ImageItem(x, y, w, h, b64=d.get("data"), item_id=item_id,
                          title=d.get("title", ""), description=d.get("description", ""),
                          show_title=d.get("show_title", True),
                          show_description=d.get("show_description", True),
                          title_font=d.get("title_font"), desc_font=d.get("description_font"),
                          title_color=d.get("title_color"), desc_color=d.get("description_color"))
    elif t == "gif":
        item = GifItem(x, y, w, h, b64=d.get("data"), item_id=item_id,
                        title=d.get("title", ""), description=d.get("description", ""),
                        show_title=d.get("show_title", True),
                        show_description=d.get("show_description", True),
                        title_font=d.get("title_font"), desc_font=d.get("description_font"),
                        title_color=d.get("title_color"), desc_color=d.get("description_color"))
    elif t == "video":
        item = VideoItem(x, y, w, h, b64=d.get("data"), item_id=item_id,
                          title=d.get("title", ""), description=d.get("description", ""),
                          show_title=d.get("show_title", True),
                          show_description=d.get("show_description", True),
                          title_font=d.get("title_font"), desc_font=d.get("description_font"),
                          title_color=d.get("title_color"), desc_color=d.get("description_color"))
    elif t == "drawing":
        item = DrawingItem(x, y, w, h, strokes=d.get("strokes", []), item_id=item_id)
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
        )
    elif t == "board":
        item = BoardCardItem(x, y, w, h, title=d.get("title", "Board"), subitems=d.get("subitems", []), item_id=item_id)
    elif t == "board_link":
        item = BoardLinkItem(
            x, y, w, h, title=d.get("title", "Board"), target_file=d.get("target_file", ""),
            item_id=item_id, thumb_mime=d.get("thumb_mime"), thumb_data=d.get("thumb_data"),
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
    return item


# --------------------------------------------------------------------------
# Scene
# --------------------------------------------------------------------------

class MindMapScene(QGraphicsScene):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setSceneRect(-5000, -5000, 10000, 10000)
        self.setBackgroundBrush(QColor("#101012"))
        self.draw_mode = False
        self.brush_color = QColor("#ffffff")
        self.brush_width = 4
        self.brush_type = "pen"  # pen, marker, highlighter
        self.brush_opacity = 1.0  # 0..1, set via the opacity slider
        self._current_stroke_points = []
        self._current_preview_item = None

    # -- background dot grid ------------------------------------------
    # Dots are drawn in *scene* coordinates with a non-cosmetic pen, so
    # they are transformed together with everything else: zooming in
    # (Ctrl+Wheel) makes the dots visibly bigger and further apart on
    # screen, exactly like the reference screenshots.
    GRID_SPACING = 40
    DOT_SIZE = 2.4

    def drawBackground(self, painter, rect):
        super().drawBackground(painter, rect)
        grid = self.GRID_SPACING
        painter.setRenderHint(QPainter.Antialiasing, False)
        pen = QPen(QColor(255, 255, 255, 40))
        pen.setWidthF(self.DOT_SIZE)
        pen.setCapStyle(Qt.SquareCap)
        painter.setPen(pen)

        left = int(rect.left()) - (int(rect.left()) % grid)
        top = int(rect.top()) - (int(rect.top()) % grid)
        x = left
        while x < rect.right():
            y = top
            while y < rect.bottom():
                painter.drawPoint(QPointF(x, y))
                y += grid
            x += grid

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

    def mousePressEvent(self, event):
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
        self.clearSelection()
        merged.setSelected(True)
        return merged

    # -- drag a component onto a board card to nest it -----------------
    def item_drag_released(self, item):
        if isinstance(item, BoardCardItem):
            return
        try:
            center = item.mapToScene(item.rect().center())
        except Exception:
            return
        for other in self.items(center):
            if isinstance(other, BoardCardItem) and other is not item:
                sub = component_to_subitem(item)
                if sub is not None:
                    # Insert at the slot the user was hovering over
                    # (shown live by the insertion preview line) rather
                    # than always appending to the end of the card.
                    local_y = other.mapFromScene(center).y()
                    idx = other._subitem_insert_index(local_y)
                    other.add_subitem(sub, index=idx)
                    other.clear_insert_preview()
                    self.removeItem(item)
                break

    # -- helpers ----------------------------------------------------------
    def all_component_items(self):
        return [it for it in self.items() if isinstance(it, BaseComponentItem)]

    def serialize(self):
        return {"items": [it.serialize() for it in self.all_component_items()]}

    def clear_board(self):
        for it in list(self.all_component_items()):
            self.removeItem(it)

    def load(self, data):
        self.clear_board()
        for d in data.get("items", []):
            item = deserialize_component(d)
            if item:
                self.addItem(item)


# --------------------------------------------------------------------------
# View (canvas): middle-mouse panning, ctrl+wheel zoom, OS file drop
# --------------------------------------------------------------------------

class MindMapView(QGraphicsView):
    def __init__(self, scene, main_window, parent=None):
        super().__init__(scene, parent)
        self.main_window = main_window
        self.setRenderHints(QPainter.Antialiasing | QPainter.SmoothPixmapTransform)
        self.setDragMode(QGraphicsView.RubberBandDrag)
        self.setAcceptDrops(True)
        self.setTransformationAnchor(QGraphicsView.AnchorUnderMouse)
        self.setResizeAnchor(QGraphicsView.AnchorUnderMouse)
        self._panning = False
        self._pan_start = QPoint()

    def wheelEvent(self, event):
        if event.modifiers() & Qt.ControlModifier:
            factor = 1.15 if event.angleDelta().y() > 0 else 1 / 1.15
            self.scale(factor, factor)
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
        cx, cy = state.get("center_x"), state.get("center_y")
        if cx is not None and cy is not None:
            self.centerOn(cx, cy)

    def mousePressEvent(self, event):
        if event.button() == Qt.MiddleButton:
            self._panning = True
            self._pan_start = event.position().toPoint()
            self.setCursor(Qt.ClosedHandCursor)
            event.accept()
            return
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
            # A rectangular selection just finished: if it caught more than
            # one freehand drawing, treat them as a single object from now
            # on (instead of the old nearest-object-guessing merge).
            self.scene().merge_selected_drawings()

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
  .text-note {{ border-radius:8px; padding:10px; color:#222; box-shadow:0 2px 6px rgba(0,0,0,.4); white-space:pre-wrap; overflow:auto; }}
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
  .board-body {{ padding:8px; overflow:auto; height:calc(100% - 40px); }}
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
    var delta = e.deltaY < 0 ? 1.1 : 0.9;
    scale = Math.min(4, Math.max(0.15, scale * delta));
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
}})();
</script>
</body>
</html>
"""


def build_html_document(data):
    comps_html = []
    xs0, ys0, xs1, ys1 = [], [], [], []
    for d in data.get("items", []):
        item = deserialize_component(d)
        if item:
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
        components="\n".join(comps_html), json_data=json_data, bounds_json=bounds_json,
        view_json=view_json, breadcrumb_html=breadcrumb_html,
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


class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("OpenNote \u2014 Milanote-style Mind Map")
        self.resize(1440, 900)
        self.scene = MindMapScene(self)
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
        # The most recent text item that was genuinely in edit mode -
        # kept around (independent of _active_label_arrow's narrower
        # "is this arrow's label the font-panel target" bookkeeping) so
        # a toolbar widget that must grab real keyboard focus (the font
        # combo, to let you type/search) can hand focus back afterward -
        # see _restore_text_edit_focus.
        self._last_edited_text_item = None

        self._build_toolbar()
        self.scene.selectionChanged.connect(self.on_selection_changed)
        # Entering/leaving in-place text edit mode doesn't change the
        # scene's *selection*, only its focus item - but the Color button
        # needs to know about it too (it targets text color while editing,
        # component color otherwise), so refresh on focus changes as well.
        self.scene.focusItemChanged.connect(self.on_selection_changed)
        self._build_menu()
        self.statusBar().showMessage(
            "Ready \u2014 Middle-mouse drag to pan \u00b7 Ctrl+Wheel to zoom \u00b7 Ctrl+D duplicate \u00b7 Drag a card onto a Board to nest it"
        )
        self._update_breadcrumb_bar()

    # -- UI construction --------------------------------------------------
    def _build_menu(self):
        m = self.menuBar()
        file_menu = m.addMenu("&File")
        file_menu.addAction("New Board", self.new_board, QKeySequence.New)
        file_menu.addAction("New Project (Choose Folder)...", self.new_project)
        file_menu.addAction("Open...", self.open_board, QKeySequence.Open)
        file_menu.addAction("Save", self.save_board, QKeySequence.Save)
        file_menu.addAction("Save As...", self.save_board_as, QKeySequence.SaveAs)
        file_menu.addSeparator()
        file_menu.addAction("Exit", self.close)

        edit_menu = m.addMenu("&Edit")
        edit_menu.addAction("Copy", self.copy_selection, QKeySequence.Copy)
        edit_menu.addAction("Paste", self.paste_clipboard, QKeySequence.Paste)
        edit_menu.addAction("Duplicate", self.duplicate_selection, QKeySequence("Ctrl+D"))
        edit_menu.addAction("Delete", self.delete_selection, QKeySequence.Delete)

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

        draw_tb.addWidget(QLabel("  Size: "))
        self.size_slider = QSlider(Qt.Horizontal)
        self.size_slider.setRange(1, 40)
        self.size_slider.setValue(4)
        self.size_slider.setFixedWidth(140)
        # Same reasoning as color_btn's NoFocus above: a QSlider grabs
        # keyboard focus by default, which would end whatever text item
        # is currently being edited (its focusOutEvent drops edit mode)
        # the instant the slider is touched - most visibly breaking an
        # Arrow's label, whose font controls only show up while it's
        # actively focused/being edited.
        self.size_slider.setFocusPolicy(Qt.NoFocus)
        self.size_slider.valueChanged.connect(self.on_size_changed)
        draw_tb.addWidget(self.size_slider)

        draw_tb.addWidget(QLabel("  Opacity: "))
        self.opacity_slider = QSlider(Qt.Horizontal)
        self.opacity_slider.setRange(5, 100)
        self.opacity_slider.setValue(100)
        self.opacity_slider.setFixedWidth(120)
        self.opacity_slider.setFocusPolicy(Qt.NoFocus)
        self.opacity_slider.valueChanged.connect(self.on_opacity_changed)
        draw_tb.addWidget(self.opacity_slider)

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

        # -- text formatting controls (Text Note / Text only) -----------
        # Hidden by default; on_selection_changed shows them only while a
        # text component is selected, so they don't clutter the toolbar
        # the rest of the time. Color/Size/Opacity above double up for
        # text too (text color, font size, item opacity) the same way
        # they already double up for drawings/arrows.
        self.text_format_sep = draw_tb.addSeparator()

        draw_tb.addWidget(QLabel("  Font: "))
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

        self.link_btn = QToolButton()
        self.link_btn.setText("Link")
        self.link_btn.setToolTip("Add / edit hyperlink")
        self.link_btn.setFocusPolicy(Qt.NoFocus)
        self.link_btn.clicked.connect(self.on_hyperlink_clicked)
        self.link_action = draw_tb.addWidget(self.link_btn)

        self._font_format_actions = [
            self.text_format_sep, self.font_action,
            self.bold_action, self.italic_action, self.underline_action,
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
        if editing_item is not None:
            self._last_edited_text_item = editing_item
        elif self._last_edited_text_item is not None:
            parent = self._last_edited_text_item.parentItem()
            if parent not in all_sel:
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
        # Anything with a font to edit via the toolbar's Font/B/I/U/Size
        # controls - Text Note, plain Text, Table (whose cells each carry
        # their own font - see TableItem.font_targets), media items, and
        # an arrow's label while it's being edited.
        font_sel = text_sel + table_sel + media_sel + arrow_label_sel
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
        if arrow_sel:
            self.line_style_combo.blockSignals(True)
            idx = self.line_style_combo.findData(arrow_sel[0].line_style)
            self.line_style_combo.setCurrentIndex(max(0, idx))
            self.line_style_combo.blockSignals(False)

        self._text_note_selection = text_note_sel or None
        self.title_checkbox_action.setVisible(bool(text_note_sel))
        if text_note_sel:
            self.title_checkbox.blockSignals(True)
            self.title_checkbox.setChecked(text_note_sel[0].show_title)
            self.title_checkbox.blockSignals(False)

        self.arrow_label_checkbox_action.setVisible(bool(arrow_sel))
        if arrow_sel:
            self.arrow_label_checkbox.blockSignals(True)
            self.arrow_label_checkbox.setChecked(arrow_sel[0].show_label)
            self.arrow_label_checkbox.blockSignals(False)

        self._media_selection = media_sel or None
        self.media_title_checkbox_action.setVisible(bool(media_sel))
        self.media_desc_checkbox_action.setVisible(bool(media_sel))
        if media_sel:
            self.media_title_checkbox.blockSignals(True)
            self.media_title_checkbox.setChecked(media_sel[0].show_title)
            self.media_title_checkbox.blockSignals(False)
            self.media_desc_checkbox.blockSignals(True)
            self.media_desc_checkbox.setChecked(media_sel[0].show_description)
            self.media_desc_checkbox.blockSignals(False)

        # Only show the leading separator (and its extra spacing) when at
        # least one of the checkboxes it introduces is actually visible -
        # otherwise it'd leave a stray divider mark on the toolbar even
        # with nothing selected.
        self.checkbox_group_sep.setVisible(bool(text_note_sel or arrow_sel or media_sel))

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
                else:
                    default = getattr(first, "DEFAULT_COLOR", None) or "#ffffff"
                    col = QColor(first.color) if first.color else QColor(default)
                self.color_btn.setStyleSheet(f"background-color:{col.name()}; border:1px solid #888;")
            self.size_slider.blockSignals(True)
            self.size_slider.setValue(int(max(1, min(40, round(font.pointSizeF())))))
            self.size_slider.blockSignals(False)
            self.opacity_slider.blockSignals(True)
            self.opacity_slider.setValue(int(max(5, min(100, round(first.opacity() * 100)))))
            self.opacity_slider.blockSignals(False)
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
            self.opacity_slider.blockSignals(True)
            self.opacity_slider.setValue(int(max(5, min(100, round(col.alphaF() * 100)))))
            self.opacity_slider.blockSignals(False)
        elif other_sel:
            first = other_sel[0]
            col = QColor(first.color) if getattr(first, "color", None) else QColor(getattr(first, "DEFAULT_COLOR", None) or "#ffffff")
            self.color_btn.setStyleSheet(f"background-color:{col.name()}; border:1px solid #888;")
        elif editing_item is None:
            self._set_brush_color(self.scene.brush_color)
            self.size_slider.blockSignals(True)
            self.size_slider.setValue(self.scene.brush_width)
            self.size_slider.blockSignals(False)
            self.opacity_slider.blockSignals(True)
            self.opacity_slider.setValue(int(self.scene.brush_opacity * 100))
            self.opacity_slider.blockSignals(False)

    def pick_color(self):
        editing_item = self._focused_text_item()
        if editing_item is not None:
            # Editing text (or a selection inside it): change the TEXT
            # color of whatever's being edited, regardless of which
            # component type it belongs to - never the component's own
            # background/border color while in this mode.
            parent = editing_item.parentItem()
            start = editing_item.defaultTextColor()
            color = QColorDialog.getColor(start, self, "Pick text color")
            if not color.isValid():
                return
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

    def on_hyperlink_clicked(self):
        if not self._text_selection:
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

    def on_line_style_changed(self, index):
        if not self._arrow_selection:
            return
        ls = self.line_style_combo.itemData(index)
        if not ls:
            return
        for it in self._arrow_selection:
            it.line_style = ls
            it.update()

    def on_title_toggled(self, checked):
        if not getattr(self, "_text_note_selection", None):
            return
        for it in self._text_note_selection:
            if it.show_title != checked:
                it._toggle_show_title()

    def on_arrow_label_toggled(self, checked):
        if not self._arrow_selection:
            return
        for it in self._arrow_selection:
            if it.show_label != checked:
                it._toggle_show_label()

    def on_media_title_toggled(self, checked):
        if not getattr(self, "_media_selection", None):
            return
        for it in self._media_selection:
            if it.show_title != checked:
                it._toggle_show_title()

    def on_media_desc_toggled(self, checked):
        if not getattr(self, "_media_selection", None):
            return
        for it in self._media_selection:
            if it.show_description != checked:
                it._toggle_show_description()

    def toggle_draw_mode(self, checked):
        self.scene.draw_mode = checked
        self.view.setDragMode(QGraphicsView.NoDrag if checked else QGraphicsView.RubberBandDrag)
        self.brush_label_action.setVisible(checked)
        self.brush_combo_action.setVisible(checked)
        self.statusBar().showMessage(
            "Draw mode ON \u2014 click and drag on the canvas to sketch" if checked else "Ready"
        )

    # -- component creation ---------------------------------------------
    def _viewport_center_scene(self):
        return self.view.mapToScene(self.view.viewport().rect().center())

    def add_text_note(self):
        pos = self._viewport_center_scene()
        item = TextNoteItem(pos.x() - 110, pos.y() - 70)
        self.scene.addItem(item)

    def add_text(self):
        pos = self._viewport_center_scene()
        item = PlainTextItem(pos.x() - 110, pos.y() - 25)
        self.scene.addItem(item)

    def add_board_card(self):
        pos = self._viewport_center_scene()
        item = BoardCardItem(pos.x() - 140, pos.y() - 160)
        self.scene.addItem(item)

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
            stroke_width=self.scene.brush_width,
            style=style,
        )
        self.scene.addItem(item)
        self.scene.clearSelection()
        item.setSelected(True)

    def create_item_from_file(self, path, scene_pos):
        ext = os.path.splitext(path)[1].lower()
        try:
            with open(path, "rb") as f:
                data = f.read()
        except Exception as e:
            QMessageBox.warning(self, "Error", f"Could not read file: {e}")
            return None
        if ext in GIF_EXTS:
            item = GifItem(scene_pos.x() - 120, scene_pos.y() - 90, gif_bytes=data,
                            title="Title", description="description...")
        elif ext in VIDEO_EXTS:
            item = VideoItem(scene_pos.x() - 160, scene_pos.y() - 110, video_bytes=data,
                              title="Title", description="description...")
        elif ext in IMAGE_EXTS:
            pm = QPixmap()
            pm.loadFromData(data)
            item = ImageItem(scene_pos.x() - 120, scene_pos.y() - 90, pixmap=pm,
                              title="Title", description="description...")
        else:
            QMessageBox.information(self, "Unsupported file", f"Unsupported file type: {ext}")
            return None
        self.scene.addItem(item)
        return item

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
                new_item.setSelected(True)

    def delete_selection(self):
        for it in list(self.scene.selectedItems()):
            self.scene.removeItem(it)

    def keyPressEvent(self, event):
        if event.key() in (Qt.Key_Delete, Qt.Key_Backspace):
            focus_item = self.scene.focusItem()
            if not isinstance(focus_item, QGraphicsTextItem):
                self.delete_selection()
        super().keyPressEvent(event)

    # -- file save / load -----------------------------------------------
    def new_board(self):
        if QMessageBox.question(self, "New board", "Clear the current board?") == QMessageBox.Yes:
            self.scene.clear_board()
            self.current_file = None
            self.breadcrumb = [{"name": "Untitled", "file": None}]
            self._update_breadcrumb_bar()
            self.setWindowTitle("OpenNote \u2014 Milanote-style Mind Map")

    def new_project(self):
        """Start a brand-new project: clear the board, then immediately
        ask for a project folder (existing or newly created) and a name
        for this first board file inside it - see
        choose_or_create_project_folder/_ensure_project_and_file, and
        BoardLinkItem for how sibling boards later attach to that same
        folder."""
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
        self.setWindowTitle(f"OpenNote \u2014 {basename}")
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
            self.setWindowTitle(f"OpenNote \u2014 {basename}")
            self._update_breadcrumb_bar()

    def _write_html(self, path):
        data = self.scene.serialize()
        data["view"] = self.view.current_view_state()
        data["breadcrumb"] = self.breadcrumb
        html = build_html_document(data)
        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write(html)
            self.statusBar().showMessage(f"Saved: {path}", 4000)
        except Exception as e:
            QMessageBox.critical(self, "Save failed", str(e))

    def open_board(self):
        path, _ = QFileDialog.getOpenFileName(self, "Open board", "", "HTML files (*.html)")
        if not path:
            return
        self._load_board_file(path, error_title="Open failed")

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
        self._load_board_file(path, error_title="Navigation failed")

    def _load_board_file(self, path, error_title="Open failed"):
        try:
            with open(path, "r", encoding="utf-8") as f:
                html = f.read()
            data = extract_scene_data(html)
            if data is None:
                QMessageBox.warning(self, error_title, "No board data found in this HTML file.")
                return
            self.scene.load(data)
            self.view.apply_view_state(data.get("view"))
            self.current_file = path
            self.project_dir = os.path.dirname(path)
            basename = os.path.basename(path)
            self.breadcrumb = data.get("breadcrumb") or [
                {"name": os.path.splitext(basename)[0], "file": basename}
            ]
            self.setWindowTitle(f"OpenNote \u2014 {basename}")
            self.statusBar().showMessage(f"Opened: {path}", 4000)
            self._update_breadcrumb_bar()
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
