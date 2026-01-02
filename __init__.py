bl_info = {
    "name": "Blender Shapekey Add-Ons",
    "author": "LupisYoung",
    "version": (1, 5, 0),
    "blender": (3, 6, 0),
    "location": "Object Data Properties > Shape Keys",
    "description": "Organize, search/filter, group-tag, batch-rename, sort, and bulk-edit shapekeys.",
    "warning": "",
    "doc_url": "https://github.com/LupisYoung/Blender-Shapekey-Addons",
    "tracker_url": "https://github.com/LupisYoung/Blender-Shapekey-Addons/issues",
    "support": "COMMUNITY",
    "category": "Object",
}

__version__ = ".".join(map(str, bl_info.get("version", (0, 0, 0))))

import bpy
import json
import urllib.request
import urllib.error
from bpy.types import Operator, Panel, PropertyGroup, UIList, AddonPreferences
import os, sys, re
import time
from mathutils import Vector
from mathutils.kdtree import KDTree
from mathutils.bvhtree import BVHTree
from bpy.props import (
    BoolProperty,
    StringProperty,
    IntProperty,
    EnumProperty,
    FloatProperty,
    CollectionProperty,
    PointerProperty,
)

try:
    import tomllib as _toml
except Exception:
    _toml = None

_DBL_CLICK = {"name": "", "t": 0.0}
_DBL_THRESHOLD = 0.30

# =====================================================
# Helpers & state
# =====================================================

GITHUB_REPO = "LupisYoung/Blender-Shapekey-Addons"
GITHUB_LATEST_API = f"https://api.github.com/repos/{GITHUB_REPO}/releases/latest"
GITHUB_RELEASES_URL = f"https://github.com/{GITHUB_REPO}/releases"

_ADDON_ID = __package__ or __name__.split(".", 1)[0]

_MANIFEST_VERSION_CACHE_STR = None
_MANIFEST_VERSION_CACHE_TUP = None

_FACE_TEMPLATE_KEYS = {
    "UE": [
        "EyeLookOut", "EyeLookIn", "EyeLookUp", "EyeLookDown",
        "EyeClosed",
        "EyeSquint",
        "EyeWide",
        "EyeDilation",
        "EyeConstrict",
        "BrowPinch",
        "BrowLowerer",
        "BrowInnerUp",
        "BrowOuterUp",
        "NoseSneer",
        "NasalDilation",
        "NasalConstrict",
        "CheekSquint",
        "CheekPuff",
        "CheekSuck",
        "JawOpen", "MouthClosed",
        "JawRight", "JawLeft", "JawForward", "JawBackward",
        "JawClench", "JawMandibleRaise",
        "LipSuckUpper",
        "LipSuckLower",
        "LipSuckCorner",
        "LipFunnelUpper",
        "LipFunnelLower",
        "LipPuckerUpper",
        "LipPuckerLower",
        "MouthUpperUp",
        "MouthLowerDown",
        "MouthUpperDeepen",
        "MouthUpper",
        "MouthLower",
        "MouthCornerPull",
        "MouthCornerSlant",
        "MouthFrown",
        "MouthStretch",
        "MouthDimple",
        "MouthRaiserUpper", "MouthRaiserLower",
        "MouthPress",
        "MouthTightener",
        "TongueOut",
        "TongueUp", "TongueDown", "TongueRight", "TongueLeft",
        "TongueRoll", "TongueBendDown", "TongueCurlUp",
        "TongueSquish", "TongueFlat",
        "TongueTwist",
    ],

    "ARKit": [
        "eyeBlinkLeft", "eyeLookDownLeft", "eyeLookInLeft", "eyeLookOutLeft",
        "eyeLookUpLeft", "eyeSquintLeft", "eyeWideLeft",
        "eyeBlinkRight", "eyeLookDownRight", "eyeLookInRight", "eyeLookOutRight",
        "eyeLookUpRight", "eyeSquintRight", "eyeWideRight",
        "jawForward", "jawLeft", "jawRight", "jawOpen",
        "mouthClose", "mouthFunnel", "mouthPucker",
        "mouthLeft", "mouthRight",
        "mouthSmileLeft", "mouthSmileRight",
        "mouthFrownLeft", "mouthFrownRight",
        "mouthDimpleLeft", "mouthDimpleRight",
        "mouthStretchLeft", "mouthStretchRight",
        "mouthRollLower", "mouthRollUpper",
        "mouthShrugLower", "mouthShrugUpper",
        "mouthPressLeft", "mouthPressRight",
        "mouthLowerDownLeft", "mouthLowerDownRight",
        "mouthUpperUpLeft", "mouthUpperUpRight",
        "browDownLeft", "browDownRight", "browInnerUp", "browOuterUpLeft", "browOuterUpRight",
        "cheekPuff", "cheekSquintLeft", "cheekSquintRight",
        "noseSneerLeft", "noseSneerRight",
        "tongueOut",
    ],

    "SRanipal": [
        "Eye_Left_Blink", "Eye_Left_Wide", "Eye_Left_squeeze",
        "Eye_Left_Down", "Eye_Left_Up", "Eye_Left_Left", "Eye_Left_Right",
        "Eye_Left_Look_Down", "Eye_Left_Look_Up",
        "Eye_Left_Dilation", "Eye_Left_Constrict",
        "Eye_Right_Blink", "Eye_Right_Wide", "Eye_Right_squeeze",
        "Eye_Right_Down", "Eye_Right_Up", "Eye_Right_Left", "Eye_Right_Right",
        "Eye_Right_Look_Down", "Eye_Right_Look_Up",
        "Eye_Right_Dilation", "Eye_Right_Constrict",
        "Cheek_Puff_Right", "Cheek_Puff_Left", "Cheek_Suck",
        "Jaw_Open", "Jaw_Forward", "Jaw_Left", "Jaw_Right",
        "Mouth_Ape_Shape",
        "Mouth_Upper_Up_Right", "Mouth_Upper_Up_Left",
        "Mouth_Lower_Down_Right", "Mouth_Lower_Down_Left",
        "Mouth_Upper_Inside", "Mouth_Lower_Inside",
        "Mouth_Upper_Overturn", "Mouth_Lower_Overturn",
        "Mouth_Pout",
        "Mouth_Smile_Right", "Mouth_Smile_Left",
        "Mouth_Sad_Right", "Mouth_Sad_Left",
        "Mouth_Lower_Overlay",
        "Tongue_LongStep1", "Tongue_LongStep2",
        "Tongue_Down", "Tongue_Up",
        "Tongue_Left", "Tongue_Right",
        "Tongue_Roll",
    ],
}

def _manifest_path():
    pkg_dir = os.path.dirname(os.path.abspath(__file__))
    p = os.path.join(pkg_dir, "blender_manifest.toml")
    return p if os.path.isfile(p) else None

def _manifest_version_str():
    """Return exact version string from blender_manifest.toml (e.g. '1.3.0-pre1'), or ''."""
    global _MANIFEST_VERSION_CACHE_STR
    if _MANIFEST_VERSION_CACHE_STR is not None:
        return _MANIFEST_VERSION_CACHE_STR

    path = _manifest_path()
    if not path:
        _MANIFEST_VERSION_CACHE_STR = ""
        return _MANIFEST_VERSION_CACHE_STR

    try:
        with open(path, "rb") as f:
            if _toml:
                data = _toml.load(f)
                v = (data.get("version")
                     or (data.get("addon") or {}).get("version")
                )
                _MANIFEST_VERSION_CACHE_STR = str(v or "").strip()
            else:
                raw = f.read().decode("utf-8", "ignore")
                m = re.search(r'^\s*version\s*=\s*"([^"]+)"\s*$', raw, flags=re.M)
                _MANIFEST_VERSION_CACHE_STR = (m.group(1).strip() if m else "")
    except Exception:
        _MANIFEST_VERSION_CACHE_STR = ""
    return _MANIFEST_VERSION_CACHE_STR

def _parse_semver_to_tuple(vstr: str):
    """
    Convert '1.3.0-pre1' -> (1,3,0, 'pre1') and comparison tuple (1,3,0,-1)
    """
    if not vstr:
        return (0, 0, 0, ""), (0, 0, 0, 0)
    t = vstr[1:] if vstr[:1].lower() == "v" else vstr
    core = re.split(r'[-+]', t, maxsplit=1)[0]
    parts = core.split(".")[:3]
    nums = [int(p) if p.isdigit() else 0 for p in parts] + [0, 0, 0]
    major, minor, patch = nums[:3]
    suffix = ""
    m = re.search(r'-(.+)$', t)
    if m: suffix = m.group(1)
    cmp = (major, minor, patch, -1 if suffix else 0)
    return (major, minor, patch, suffix), cmp

def _current_version_tuple():
    """
    Prefer version from blender_manifest.toml.
    Falls back to bl_info/ __version__ if manifest missing.
    """
    vstr = _manifest_version_str()
    if vstr:
        _full, cmp = _parse_semver_to_tuple(vstr)
        return tuple(cmp[:3])

    try:
        vi = bl_info.get("version", (0, 0, 0))
        return tuple(int(x) for x in list(vi[:3]) + [0, 0])[:3]
    except Exception:
        pass

    vstr = globals().get("__version__", "")
    if isinstance(vstr, str) and vstr:
        full, _cmp = _parse_semver_to_tuple(vstr)
        return tuple(full[:3])

    return (0, 0, 0)

def current_version_display():
    """Human-readable version for UI—shows prerelease if present."""
    vstr = _manifest_version_str()
    if vstr:
        return vstr
    v = bl_info.get("version", (0, 0, 0))
    return ".".join(map(str, v))


def _parse_version_tag(tag: str):
    """Parse GitHub tags like 'v1.3.0-pre1' into a comparison tuple."""
    if not tag:
        return (0, 0, 0, 0)
    _full, cmp = _parse_semver_to_tuple(tag)
    return cmp


def _fetch_latest_tag():
    """Return latest release tag_name from GitHub Releases API, or '' on failure."""
    ua = f"Blender-Shapekey-Add-Ons/{_manifest_version_str() or '0.0.0'}"
    req = urllib.request.Request(GITHUB_LATEST_API, headers={"User-Agent": ua})
    try:
        with urllib.request.urlopen(req, timeout=6) as resp:
            data = json.loads(resp.read().decode("utf-8", "ignore"))
        return data.get("tag_name") or ""
    except Exception:
        return ""


def shapekey_max_delta(obj, key):
    """
    Return the maximum distance any vertex in this key
    has from the Basis key.
    """
    sk = getattr(obj.data, "shape_keys", None)
    if not sk or not key:
        return 0.0

    basis = sk.key_blocks[0]
    if key == basis:
        return 0.0

    kd = key.data
    bd = basis.data

    if len(kd) != len(bd):
        return 1e9

    max_d = 0.0
    for i in range(len(kd)):
        d = (kd[i].co - bd[i].co).length
        if d > max_d:
            max_d = d

    return max_d


def obj_world_size(obj):
    """Rough scale of object based on bounding box diagonal in world space."""
    if not obj or not obj.type == 'MESH':
        return 1.0
    mw = obj.matrix_world
    bb = [mw @ Vector(corner) for corner in obj.bound_box]
    diag = (bb[6] - bb[0]).length
    return diag if diag > 0.0 else 1.0


def build_basis_bvh(obj):
    """
    Build a BVHTree from the Basis shapekey (or mesh vertices if no keys),
    returning (bvh, triangles, basis_world_coords).
    """
    me = obj.data
    sk = getattr(me, "shape_keys", None)
    if sk and sk.key_blocks:
        basis = sk.key_blocks[0]
        coords_local = [kd.co.copy() for kd in basis.data]
    else:
        coords_local = [v.co.copy() for v in me.vertices]

    mw = obj.matrix_world
    verts_world = [mw @ co for co in coords_local]

    triangles = []
    for poly in me.polygons:
        v_idx = poly.vertices
        if len(v_idx) == 3:
            triangles.append([v_idx[0], v_idx[1], v_idx[2]])
        elif len(v_idx) > 3:
            for i in range(1, len(v_idx) - 1):
                triangles.append([v_idx[0], v_idx[i], v_idx[i + 1]])

    if not triangles:
        return None, [], verts_world

    bvh = BVHTree.FromPolygons(verts_world, triangles, all_triangles=False)
    return bvh, triangles, verts_world


def barycentric_coords(p, a, b, c):
    """
    Return barycentric coords (u, v, w) of point p in triangle (a, b, c).
    Returns None if triangle is degenerate.
    """
    v0 = b - a
    v1 = c - a
    v2 = p - a
    
    d00 = v0.dot(v0)
    d01 = v0.dot(v1)
    d11 = v1.dot(v1)
    d20 = v2.dot(v0)
    d21 = v2.dot(v1)
    
    denom = d00 * d11 - d01 * d01
    
    if abs(denom) < 1e-12:
        return None
    
    v = (d11 * d20 - d01 * d21) / denom
    w = (d00 * d21 - d01 * d20) / denom
    u = 1.0 - v - w
    
    return u, v, w


def sko_set_status_text(context, text: str | None):
    """
    Set status text in a Blender-version-safe way.
    - Blender 4.x: context.workspace.status_text_set(...)
    - Blender 3.x: context.window_manager.status_text_set(...)
    """
    # New API (4.0+)
    ws = getattr(context, "workspace", None)
    if ws and hasattr(ws, "status_text_set"):
        ws.status_text_set(text)
        return

    # Older API (3.x)
    wm = getattr(context, "window_manager", None)
    if wm and hasattr(wm, "status_text_set"):
        wm.status_text_set(text)


def _elide(text: str, max_len: int = 14) -> str:
    text = text or ""
    return text if len(text) <= max_len else (text[:max_len - 1] + "…")


def _sko_split_keyblock_half(obj, src_key, axis='X', eps=1e-4, keep_side='LEFT', use_median_plane=False):
    """
    Zero out the opposite half of src_key (relative to Basis), by copying Basis coords.
    keep_side: 'LEFT' or 'RIGHT' (negative vs positive side along the X axis).
    If use_median_plane is True, split around the median coordinate of Basis on that axis.
    """
    sk = obj.data.shape_keys
    if not sk or not src_key or src_key == sk.key_blocks[0]:
        return 0

    basis = sk.key_blocks[0]
    kd = src_key.data
    bd = basis.data
    n = len(kd)

    comp_idx = {'X': 0, 'Y': 1, 'Z': 2}.get(axis.upper(), 0)

    if use_median_plane:
        coords = [bd[i].co[comp_idx] for i in range(n)]
        coords.sort()
        mid = len(coords) // 2
        plane = (coords[mid] if (len(coords) % 2 == 1) else 0.5 * (coords[mid - 1] + coords[mid]))
    else:
        plane = 0.0

    changed = 0
    for i in range(n):
        v = bd[i].co[comp_idx] - plane
        if keep_side == 'LEFT':
            kill = (v > eps)
        else:
            kill = (v < -eps)

        if kill:
            kd[i].co = bd[i].co
            changed += 1

    return changed


def get_target_keys(context, *, require_selected=True, visible_only=True,
                    fallback_to_active=True, exclude_basis=True):
    obj = context.object
    if not obj or obj.type != 'MESH':
        return []

    pool = filtered_keys(context, obj) if visible_only else list(iter_keyblocks(obj))
    targets = [k for k in pool if get_sel(k)] if require_selected else list(pool)

    if fallback_to_active and not targets:
        ak = getattr(obj, "active_shape_key", None)
        if ak and ((not exclude_basis) or not is_basis_key(obj, ak)):
            if (not visible_only) or (ak in pool):
                targets = [ak]

    if exclude_basis:
        targets = [k for k in targets if not is_basis_key(context.object, k)]
    return targets


class SKO_OT_CheckUpdates(bpy.types.Operator):
    bl_idname = "shapekey_organizer.check_updates"
    bl_label = "Check for Updates"
    bl_description = "Check GitHub for a newer version of this add-on"
    bl_options = {'INTERNAL'}

    silent_if_latest: bpy.props.BoolProperty(
        name="Silent If Latest",
        description="If enabled, do not show a popup unless a newer version is available",
        default=False,
        options={'SKIP_SAVE'},
    )

    def execute(self, context):
        current_str = current_version_display()
        current_cmp = _parse_version_tag(current_str)
        latest_tag = _fetch_latest_tag()
        latest_cmp = _parse_version_tag(latest_tag)

        if latest_tag == "":
            msg = "Could not determine latest version (GitHub API unavailable)."
            if not self.silent_if_latest:
                self._popup(context, msg, show_open=True)
            return {'CANCELLED'}

        if latest_cmp > current_cmp:
            msg = f"New version available: {latest_tag} (current v{current_str})."
            self._popup(context, msg, show_open=True)
        else:
            msg = f"You are on the latest version (v{current_str})."
            if not self.silent_if_latest:
                self._popup(context, msg, show_open=False)
        return {'FINISHED'}

    def _popup(self, context, message, show_open=True):
        def draw(self, _ctx):
            self.layout.label(text=message)
            if show_open:
                self.layout.operator("wm.url_open", text="Open Releases").url = GITHUB_RELEASES_URL
        context.window_manager.popup_menu(draw, title="Blender Shapekey Add-Ons - Update", icon='INFO')


class SKO_AddonPreferences(AddonPreferences):
    bl_idname = _ADDON_ID

    auto_check: BoolProperty(
        name="Check on Startup",
        description="Check GitHub for updates once after loading a file",
        default=False,
    )

    def draw(self, context):
        col = self.layout.column(align=True)
        row = col.row(align=True)
        row.prop(self, "auto_check")
        row.operator("shapekey_organizer.check_updates", icon='FILE_REFRESH')


def _sko_auto_check(_dummy):
    try:
        entry = bpy.context.preferences.addons.get(_ADDON_ID)
        prefs = getattr(entry, "preferences", None)
        if getattr(prefs, "auto_check", False):
            try:
                bpy.ops.shapekey_organizer.check_updates('INVOKE_DEFAULT', silent_if_latest=True)
            except Exception:
                pass
    finally:
        try:
            bpy.app.handlers.load_post.remove(_sko_auto_check)
        except Exception:
            pass



def _on_find_change(self, context):
    """When the Find field changes, auto-select keys whose names contain it.
    Respects the case sensitivity toggle (default: case-insensitive)."""
    try:
        obj = active_obj_mesh(context)
        if not obj:
            return
        needle = self.find
        if not needle:
            return
        case_sensitive = getattr(self, 'find_case_sensitive', False)
        if not case_sensitive:
            needle_cmp = needle.lower()
        for k in iter_keyblocks(obj):
            hay = k.name if case_sensitive else k.name.lower()
            if (needle if case_sensitive else needle_cmp) in hay:
                set_sel(k, True)
    except Exception:
        pass


def active_obj_mesh(context):
    obj = context.object
    return obj if (obj and obj.type == 'MESH') else None


def iter_keyblocks(obj):
    ks = getattr(getattr(obj.data, 'shape_keys', None), 'key_blocks', None)
    return ks or []


class SKO_Item(PropertyGroup):
    key_name: StringProperty(name="Key Name")
    selected: BoolProperty(name="Selected", description="Selection state for list actions")
    group: StringProperty(name="Group", description="Optional group tag for this shapekey")


class SKO_GroupItem(PropertyGroup):
    name: StringProperty(name="Group Name", description="Custom group tag")


def _state_items():
    scn = bpy.context.scene
    return getattr(scn, 'sko_items', None)


def find_item_by_name(name: str):
    items = _state_items()
    if not items:
        return None
    for it in items:
        if it.key_name == name:
            return it
    return None


def ensure_item_by_name(name: str, create: bool = False):
    """Return state item for name. Only create when create=True (never from draw)."""
    items = _state_items()
    if items is None:
        return None
    it = find_item_by_name(name)
    if it or not create:
        return it
    it = items.add()
    it.key_name = name
    return it


def get_sel(key):
    it = find_item_by_name(key.name)
    return bool(it.selected) if it else False


def set_sel(key, val: bool):
    it = ensure_item_by_name(key.name, create=True)
    if it:
        it.selected = bool(val)


def get_group(key):
    it = find_item_by_name(key.name)
    return it.group if it else ""


def set_group(key, group_name: str):
    it = ensure_item_by_name(key.name, create=True)
    if it:
        it.group = group_name or ""


def all_groups(context):
    return getattr(context.scene, 'sko_groups', [])


def ensure_group(context, name: str):
    name = (name or "").strip()
    if not name:
        return None
    groups = all_groups(context)
    for g in groups:
        if g.name == name:
            return g
    g = groups.add()
    g.name = name
    return g


def filtered_keys(context, obj):
    ks = iter_keyblocks(obj)
    if not ks:
        return []
    props = context.scene.shapekey_organizer
    query = props.search.lower().strip()
    group = props.filter_group.strip()
    out = []
    for k in ks:
        if query and query not in k.name.lower():
            continue
        if group and get_group(k) != group:
            continue
        out.append(k)
    return out


def is_basis_key(obj, key):
    ks = getattr(getattr(obj.data, 'shape_keys', None), 'key_blocks', None)
    return bool(ks) and key == ks[0]


def _ensure_active_not_basis(obj):
    """If active key lands on Basis (index 0), push it down to index 1."""
    try:
        while obj.active_shape_key_index == 0:
            bpy.ops.object.shape_key_move(type='DOWN')
    except Exception:
        pass


def move_active_to_top_below_basis(obj):
    """Move currently active shape key to the top *below Basis* (index 1)."""
    try:
        bpy.ops.object.shape_key_move(type='TOP')
        _ensure_active_not_basis(obj)
    except Exception:
        pass

# =====================================================
# Properties
# =====================================================

class SKO_Props(PropertyGroup):
    search: StringProperty(
        name="Search",
        description="Filter shapekeys whose name contains this text (case-insensitive)",
        default="",
    )
    filter_group: StringProperty(
        name="Group",
        description="Show only keys assigned to this exact group tag",
        default="",
        options={'HIDDEN'}
    )
    anchor_index: IntProperty(
        name="Selection Anchor Index",
        description="Internal: start index for Shift-click range selection",
        default=-1,
        options={'HIDDEN'}
    )
    prefix: StringProperty(
        name="Prefix",
        description="Text to add before each selected key's name",
        default="",
    )
    suffix: StringProperty(
        name="Suffix",
        description="Text to add after each selected key's name",
        default="",
    )
    find: StringProperty(
        name="Find",
        description="Auto-selects keys whose names contain this text; used by Find & Replace",
        default="",
        update=_on_find_change,
    )
    find_case_sensitive: BoolProperty(
        name="Case Sensitive",
        description="Treat Find & Replace as case-sensitive (off = case-insensitive)",
        default=False,
    )
    replace: StringProperty(
        name="Replace",
        description="Replace the 'Find' text with this",
        default="",
    )
    sort_mode: EnumProperty(
        name="Sort",
        description="Sorting mode for selected keys",
        items=[
            ('NAME_ASC', "Name A→Z", "Sort by name ascending"),
            ('NAME_DESC', "Name Z→A", "Sort by name descending"),
            ('GROUP_LIST', "Group List → Name", "Follow custom group list order, then Name A→Z"),
        ],
        default='NAME_ASC'
    )
    auto_number_start: IntProperty(
        name="Start",
        description="Starting number for Auto-Number",
        default=1, min=0
    )
    auto_number_pad: IntProperty(
        name="Pad",
        description="Digits to pad when numbering (e.g., 2 → 01, 3 → 001)",
        default=2, min=1, max=6
    )
    slider_min: FloatProperty(
        name="Slider Min",
        description="Set slider minimum for (visible) selected keys",
        default=0.0,
        min=0.0, max=1.0,
        soft_min=0.0, soft_max=1.0,
    )
    slider_max: FloatProperty(
        name="Slider Max",
        description="Set slider maximum for (visible) selected keys",
        default=1.0,
        min=0.0, max=1.0,
        soft_min=0.0, soft_max=1.0,
    )
    affect_only_selected: BoolProperty(
        name="Only Selected",
        description="If enabled, actions only affect keys with the checkbox enabled. If off, actions affect all visible keys",
        default=True
    )
    group_search: StringProperty(
        name="Group",
        description="Group name to add/select/filter",
        default="",
    )
    group_active_index: IntProperty(
        name="Active Group Index",
        default=-1,
        options={'HIDDEN'}
    )
    transfer_target: PointerProperty(
        name="Target Object",
        description="Destination mesh object to receive selected shapekeys",
        type=bpy.types.Object,
    )
    transfer_mode: EnumProperty(
        name="Mode",
        description="How to transfer shapekeys",
        items=(
            ('MATCH_TOPOLOGY', "Match Topology",
             "Fast direct copy (requires identical vertex count and order)"),
            ('NEAREST_VERTEX', "Nearest Vertex",
             "Use nearest Basis vertex in world space"),
            ('NEAREST_BARYCENTRIC', "Nearest Barycentric",
             "Use nearest point on the source surface and barycentric interpolation"),
            ('RAYCAST', "Raycast",
             "Cast along target vertex normal to the source surface and barycentrically transfer"),
        ),
        default='MATCH_TOPOLOGY',
    )
    transfer_distance_ratio: FloatProperty(
        name="Max Distance %",
        description=(
            "Maximum distance as a percentage of source object size.\n"
            "Used to limit nearest / barycentric / raycast transfers.\n"
            "0 = no limit"
        ),
        default=0.01,
        min=0.0,
        soft_max=0.05,
    )
    transfer_create_missing: BoolProperty(
        name="Create Missing",
        description="Create shapekeys on the target if they don't exist",
        default=True,
    )
    transfer_overwrite_existing: BoolProperty(
        name="Overwrite",
        description="Overwrite existing shapekeys with the same name on the target",
        default=False,
    )
    transfer_copy_settings: BoolProperty(
        name="Copy Settings",
        description="Copy value, slider range, mute, interpolation, etc. from source keys",
        default=True,
    )

    # UI foldouts
    show_groups: BoolProperty(name="Show Groups", default=False)
    show_rename: BoolProperty(name="Show Rename", default=False)
    show_transfer: BoolProperty(name="Shape Key Transfer", default=False)
    show_batch: BoolProperty(name="Show Batch Edits", default=False)

# =====================================================
# UI List
# =====================================================

class SKO_UL_ShapeKeys(UIList):
    bl_idname = "SKO_UL_shapekeys"

    def draw_filter(self, context, layout):
        pass

    def draw_item(self, context, layout, data, item, icon, active_data, active_propname, index):
        key = item
        if not key:
            return
        sel = get_sel(key)

        obj = context.object
        is_active = (getattr(obj, "active_shape_key_index", -1) == index)
        sel = get_sel(key)
        gname = get_group(key)

        split = layout.split(factor=0.5)
        left  = split.row(align=True)
        right = split.row(align=True)

        if is_active:
            left.active = True
            right.active = True

        left_split = left.split(factor=0.75)
        name_row = left_split.row(align=True)
        name_row.alignment = 'LEFT'
        btn = name_row.operator("shapekey_organizer.key_click", text=key.name, emboss=False)
        btn.key_name = key.name
        btn.key_index = index

        group_cell = left_split.row(align=True)
        group_cell.alignment = 'RIGHT'
        if gname:
            group_cell.label(text=gname, icon='OUTLINER_COLLECTION')
        else:
            group_cell.separator()

        right.prop(key, 'value', text="")
        right.prop(key, 'mute', text="", icon_only=True, icon='HIDE_OFF')
        op = right.operator(
            "shapekey_organizer.toggle_select",
            text="",
            icon='CHECKBOX_HLT' if sel else 'CHECKBOX_DEHLT',
            depress=sel
        )
        op.key_name = key.name

    def filter_items(self, context, data, propname):
        try:
            ks = getattr(data, propname)
        except Exception:
            ks = []
        props = getattr(context.scene, 'shapekey_organizer', None)
        query = (props.search.lower().strip() if props else "")
        group = (props.filter_group.strip() if props else "")

        flt_flags = []
        for k in ks:
            show = True
            if query and query not in k.name.lower():
                show = False
            if show and group and get_group(k) != group:
                show = False
            flt_flags.append(self.bitflag_filter_item if show else 0)
        return flt_flags, list(range(len(flt_flags)))



class SKO_UL_Groups(UIList):
    bl_idname = "SKO_UL_groups"

    def draw_filter(self, context, layout):
        pass

    def filter_items(self, context, data, propname):
        self.use_filter_show = False
        self.use_filter_invert = False
        self.use_filter_sort_alpha = False
        self.use_filter_sort_reverse = False

        try:
            items = getattr(data, propname)
        except Exception:
            items = []
        flags = [self.bitflag_filter_item] * len(items)
        return flags, list(range(len(items)))

    def draw_item(self, context, layout, data, item, icon, active_data, active_propname, index):
        if not item:
            return
        row = layout.row(align=True)
        row.label(text=item.name)

# =====================================================
# Operators
# =====================================================

class SKO_OT_ToggleUseEditMode(bpy.types.Operator):
    bl_idname = "shapekey_organizer.toggle_use_edit_mode"
    bl_label = "Shape Key Edit Mode"
    bl_description = "Display shape keys in edit mode (for meshes only)."
    bl_options = {'INTERNAL', 'UNDO'}

    def execute(self, context):
        obj = context.object
        if not obj: return {'CANCELLED'}
        obj.use_shape_key_edit_mode = not obj.use_shape_key_edit_mode
        return {'FINISHED'}


class SKO_OT_ToggleShowOnly(bpy.types.Operator):
    bl_idname = "shapekey_organizer.toggle_show_only"
    bl_label = "Solo Active Shape Key"
    bl_description = "Only show the active shapekey at full value."
    bl_options = {'INTERNAL', 'UNDO'}

    def execute(self, context):
        obj = context.object
        if not obj: return {'CANCELLED'}
        obj.show_only_shape_key = not obj.show_only_shape_key
        return {'FINISHED'}


class SKO_OT_KeyActivateOrRename(Operator):
    bl_idname = "shapekey_organizer.key_click"
    bl_label = "Rename Shapekey"
    bl_description = "Single-click: set active. Quick second click: rename."
    bl_options = {'REGISTER', 'UNDO'}

    key_name: StringProperty(options={'SKIP_SAVE'})
    key_index: IntProperty(default=-1, options={'SKIP_SAVE'})
    new_name: StringProperty(name="New Name", default="", options={'SKIP_SAVE'})

    def invoke(self, context, event):
        obj = active_obj_mesh(context)
        if not obj:
            return {'CANCELLED'}

        now = time.perf_counter()
        if _DBL_CLICK["name"] == self.key_name and (now - _DBL_CLICK["t"]) <= _DBL_THRESHOLD:
            _DBL_CLICK["name"] = ""
            self.new_name = self.key_name
            return context.window_manager.invoke_props_dialog(self, width=260)

        idx = self.key_index
        if idx < 0:
            ks = getattr(getattr(obj.data, 'shape_keys', None), 'key_blocks', None) or []
            for i, kb in enumerate(ks):
                if kb.name == self.key_name:
                    idx = i
                    break
        if idx >= 0:
            obj.active_shape_key_index = idx

        _DBL_CLICK["name"] = self.key_name
        _DBL_CLICK["t"] = now
        try:
            for win in bpy.context.window_manager.windows:
                for area in win.screen.areas:
                    if area.type == 'PROPERTIES':
                        area.tag_redraw()
        except Exception:
            pass

        return {'FINISHED'}

    def draw(self, context):
        self.layout.prop(self, "new_name", text="")

    def execute(self, context):
        obj = active_obj_mesh(context)
        if not obj:
            return {'CANCELLED'}
        ks = getattr(getattr(obj.data, 'shape_keys', None), 'key_blocks', None)
        if not ks:
            return {'CANCELLED'}

        kb = ks.get(self.key_name)
        if not kb:
            return {'CANCELLED'}

        new = self.new_name.strip()
        if new and new != kb.name:
            it = ensure_item_by_name(kb.name, create=True)
            kb.name = new
            if it:
                it.key_name = new
        return {'FINISHED'}


class SKO_OT_ShapeKeyAdd(Operator):
    bl_idname = "shapekey_organizer.shape_key_add"
    bl_label = "Create Shapekey"
    bl_description = "Create a new shapekey (empty, from full mix, or from selected-only mix)"
    bl_options = {'REGISTER', 'UNDO'}

    mode: EnumProperty(
        name="Mode",
        description="How to create the new shapekey",
        items=[
            ('EMPTY',         "New (Empty)",              "Create an empty shapekey"),
            ('MIX_ALL',       "From Mix (All Visible)",   "Bake all currently visible deformation"),
            ('MIX_SELECTED',  "From Mix (Selected Only)", "Bake only selected shapekeys (optionally only visible)"),
            ('DUP_SELECTED',  "Duplicate",                "Make a copy of each selected shapekey (ignores Basis)"),
            ('DUP_MIRROR',    "Duplicate & Mirror",       "Duplicate each selected and mirror it"),
            ('SPLIT',         "Duplicate & Split",        "Duplicate each selected and zero each half by axis"),
            ('FACE_TEMPLATE', "Face Tracking Template",   "Create all empty shapekeys needed for face tracking (UE / ARKit / SRanipal)"),
        ],
        default='EMPTY'
    )

    key_name: StringProperty(
        name = "Name",
        description="Optional name; if duplicating multiple keys, this will be used as a prefix",
        default="",
        options={'SKIP_SAVE'}
    )

    # Only used when mode == MIX_SELECTED
    visible_only: BoolProperty(
        name="Only Visible (Filtered)",
        description="Limit to keys that are visible in the list (respects Search/Group filter)",
        default=False
    )
    include_zero: BoolProperty(
        name="Include Zero Values",
        description="Include selected keys even if their current value is 0.0",
        default=False
    )

    # Only used when mode == DUPLICATE
    bake_vertex_groups: BoolProperty(
        name="Bake Vertex Groups",
        description="Zero out vertices outside assigned vertex groups (for Unity compatibility)",
        default=False
    )

    # Only used when mode == DUP_SELECTED
    duplicate_suffix: StringProperty(
        name="Suffix",
        description="Suffix for duplicated names (when no explicit name is given)",
        default="",
        options={'SKIP_SAVE'},
    )

    # Only used when mode == DUP_MIRROR
    use_topology: BoolProperty(
        name="Use Topology",
        description="Use topology mapping when mirroring (safer on asymmetric meshes)",
        default=False,
        options={'SKIP_SAVE'},
    )

    # Only used when mode == SPLIT
    split_eps: FloatProperty(
        name="Threshold",
        description="Vertices within this distance of the split plane are kept (prevents tiny holes)",
        default=0.0001, min=0.0, soft_max=0.01
    )

    split_left_token: StringProperty(
        name="Left token",
        description="Text appended for the left-half key",
        default=""
    )
    split_right_token: StringProperty(
        name="Right token",
        description="Text appended for the right-half key",
        default=""
    )

    keep_original: BoolProperty(
        name="Keep Original",
        description="Keep the original shapekey after creating left/right halves",
        default=True,
        options={'SKIP_SAVE'},
    )

    use_median_plane: BoolProperty(
        name="Use Median Plane",
        description="Split relative to the mesh’s median on the axis (robust if the model isn’t centered on 0)",
        default=False,
        options={'SKIP_SAVE'},
    )

    # Only used when mode == FACE_TEMPLATE
    face_template: EnumProperty(
        name="Template",
        description="Choose which face tracking template to generate",
        items=[
            ("UE", "Unified Expressions (Symmetrical)", ""),
            ("ARKit", "ARKit", ""),
            ("SRanipal", "SRanipal", ""),
        ],
        default="UE",
    )

    skip_existing: BoolProperty(
        name="Skip Existing Keys",
        default=True,
    )

    def invoke(self, context, event):
        self.key_name = ""
        return context.window_manager.invoke_props_dialog(self, width=360)

    def draw(self, context):
        layout = self.layout
        layout.prop(self, "mode", text="")

        col = layout.column(align=True)
        if self.mode != 'SPLIT' and self.mode != 'FACE_TEMPLATE':
            name_label = "Prefix" if self.mode in {'DUP_SELECTED', 'DUP_MIRROR'} else "Name"
            col.prop(self, "key_name", text=name_label)

        if self.mode == 'MIX_SELECTED':
            box = layout.box()
            box.label(text="From Selected Options")
            row = box.row(align=False)
            row.prop(self, "visible_only")
            row.prop(self, "include_zero")

        elif self.mode == 'DUP_SELECTED':
            col.prop(self, "duplicate_suffix")
            col.prop(self, "bake_vertex_groups")
            box = layout.box()
            box.label(text="Tip: If Prefix and Suffix are empty,")
            box.label(text="Duplicates are suffixed with .001, .002, etc.")

        elif self.mode == 'DUP_MIRROR':
            col.prop(self, "duplicate_suffix", text="Suffix")
            row = layout.row(align=True)
            row.prop(self, "use_topology", text="Use Topology")
            row.prop(self, "bake_vertex_groups")
            box = layout.box()
            box.label(text="Tip: If Prefix and Suffix are empty,")
            box.label(text="Duplicates are suffixed with \"_Mirror\"")

        elif self.mode == 'SPLIT':
            col.prop(self, "split_left_token", text="Left Suffix")
            col.prop(self, "split_right_token", text="Right Suffix")

            row = layout.row(align=True)
            row.prop(self, "split_eps")

            row = layout.row(align=True)
            row.prop(self, "keep_original")
            row.prop(self, "use_median_plane")
            row.prop(self, "bake_vertex_groups")
            box = layout.box()
            box.label(text="Tip: If Left and/or Right token are empty,")
            box.label(text="Duplicates are suffixed with \"_L\" and \"_R\"")

        elif self.mode == 'FACE_TEMPLATE':
            col.prop(self, "face_template", text="Tracking Type")
            col.prop(self, "skip_existing", text="Skip Existing Keys")
            box = layout.box()
            if self.face_template == 'UE':
                box.label(text="Generates 59 base keys for symmetrical sculpting.")
                box.label(text="This template is best used with the Duplicate & Split function.")
            elif self.face_template == 'ARKit':
                box.label(text="Generates 52 keys matching Apple's ARKit shapekey set.")
            elif self.face_template == 'SRanipal':
                box.label(text="Generates 51 keys matching Vive SRanipal's shapekey set.")
            box.label(text="For detailed shapekey documentation:")
            box.operator("wm.url_open", text="Open VRCFT Documentation").url = "https://docs.vrcft.io/docs/tutorial-avatars/tutorial-avatars-extras/compatibility/overview#standard-documentation"

    def _move_key_after_source(self, obj, new_key_name, source_key_name):
        """Move a newly created shape key to appear right after its source key in the list"""
        max_attempts = 100
        attempts = 0

        while attempts < max_attempts:
            key_blocks = obj.data.shape_keys.key_blocks

            source_idx = -1
            new_idx = -1

            for i, kb in enumerate(key_blocks):
                if kb.name == source_key_name:
                    source_idx = i
                if kb.name == new_key_name:
                    new_idx = i

            if source_idx < 0 or new_idx < 0:
                return

            target_idx = source_idx + 1

            if new_idx == target_idx:
                return

            if new_idx < target_idx:
                return

            obj.active_shape_key_index = new_idx
            bpy.ops.object.shape_key_move(type='UP')

            attempts += 1

    def execute(self, context):
        obj = active_obj_mesh(context)
        if not obj:
            self.report({'WARNING'}, "Select a mesh object with shapekeys.")
            return {'CANCELLED'}

        props = context.scene.shapekey_organizer

        try:
            bpy.ops.object.mode_set(mode='OBJECT')
        except Exception:
            pass

        def _finalize_new_key():
            ks = getattr(getattr(obj.data, 'shape_keys', None), 'key_blocks', None)
            if not ks:
                return None
            new_key = ks[-1]
            if self.key_name.strip():
                new_key.name = self.key_name.strip()
            obj.active_shape_key_index = len(ks) - 1
            it = ensure_item_by_name(new_key.name, create=True)
            try:
                bpy.context.view_layer.update()
                for win in bpy.context.window_manager.windows:
                    for area in win.screen.areas:
                        if area.type in {'PROPERTIES', 'VIEW_3D'}:
                            area.tag_redraw()
            except Exception:
                pass
            return new_key

        if self.mode == 'EMPTY':
            try:
                bpy.ops.object.shape_key_add(from_mix=False)
            except Exception as e:
                self.report({'ERROR'}, f"Could not create shapekey: {e}")
                return {'CANCELLED'}
            new_key = _finalize_new_key()
            self.report({'INFO'}, f"Created shapekey: {new_key.name if new_key else '(unknown)'}")
            self.key_name = ""
            return {'FINISHED'}

        if self.mode == 'MIX_ALL':
            try:
                bpy.ops.object.shape_key_add(from_mix=True)
            except Exception as e:
                self.report({'ERROR'}, f"Could not create shapekey from mix: {e}")
                return {'CANCELLED'}
            new_key = _finalize_new_key()
            self.report({'INFO'}, f"Captured full mix to: {new_key.name if new_key else '(unknown)'}")
            self.key_name = ""
            return {'FINISHED'}

        if self.mode == 'DUP_SELECTED':
            obj = active_obj_mesh(context)
            if not obj:
                self.report({'WARNING'}, "Select a mesh object with shapekeys.")
                return {'CANCELLED'}

            ks = list(iter_keyblocks(obj))
            if not ks:
                self.report({'WARNING'}, "No shapekeys to duplicate.")
                return {'CANCELLED'}

            targets = get_target_keys(context,
                                      require_selected=props.affect_only_selected,
                                      visible_only=True,
                                      fallback_to_active=True,
                                      exclude_basis=True)
            if not targets:
                self.report({'INFO'}, "No selected shapekeys to duplicate.")
                return {'CANCELLED'}

            values_cache = {k.name: float(getattr(k, "value", 0.0)) for k in ks}

            try:
                bpy.ops.object.mode_set(mode='OBJECT')
            except Exception:
                pass

            created = 0
            last_new_name = ""

            multi = (len(targets) > 1)
            name_prefix = self.key_name.strip()
            suffix = self.duplicate_suffix

            for src in targets:
                for k in ks:
                    try:
                        k.value = 0.0
                    except Exception:
                        pass
                try:
                    src.value = 1.0
                except Exception:
                    pass

                try:
                    bpy.ops.object.shape_key_add(from_mix=True)
                except Exception as e:
                    for k in ks:
                        try:
                            k.value = values_cache.get(k.name, 0.0)
                        except Exception:
                            pass
                    self.report({'ERROR'}, f"Duplicate failed on '{src.name}': {e}")
                    return {'CANCELLED'}

                new_key = obj.data.shape_keys.key_blocks[-1]

                if multi:
                    new_key.name = f"{name_prefix}{src.name}{suffix}"
                else:
                    base_name = name_prefix if name_prefix and not multi else src.name
                    if name_prefix and not multi:
                        new_key.name = f"{name_prefix}{suffix}"
                    else:
                        new_key.name = f"{name_prefix}{src.name}{suffix}"


                try:
                    new_key.slider_min = float(getattr(src, "slider_min", 0.0))
                    new_key.slider_max = float(getattr(src, "slider_max", 1.0))
                except Exception:
                    pass
                
                if self.bake_vertex_groups and src.vertex_group:
                    vg = obj.vertex_groups.get(src.vertex_group)
                    if vg:
                        basis = obj.data.shape_keys.key_blocks[0]
                        for i in range(len(new_key.data)):
                            try:
                                weight = vg.weight(i)
                                if weight == 0:
                                    new_key.data[i].co = basis.data[i].co
                            except:
                                new_key.data[i].co = basis.data[i].co

                obj.active_shape_key_index = len(obj.data.shape_keys.key_blocks) - 1
                it = ensure_item_by_name(new_key.name, create=True)

                last_new_name = new_key.name
                self._move_key_after_source(obj, new_key.name, src.name)
                created += 1

                for k in ks:
                    try:
                        k.value = values_cache.get(k.name, 0.0)
                    except Exception:
                        pass

            try:
                bpy.context.view_layer.update()
                for win in bpy.context.window_manager.windows:
                    for area in win.screen.areas:
                        if area.type in {'PROPERTIES', 'VIEW_3D'}:
                            area.tag_redraw()
            except Exception:
                pass

            self.key_name = ""

            self.report({'INFO'}, f"Duplicated {created} shapekey(s).")
            return {'FINISHED'}

        if self.mode == 'DUP_MIRROR':
            obj = active_obj_mesh(context)
            if not obj:
                self.report({'WARNING'}, "Select a mesh object with shapekeys.")
                return {'CANCELLED'}

            ks = list(iter_keyblocks(obj))
            if not ks:
                self.report({'WARNING'}, "No shapekeys to mirror.")
                return {'CANCELLED'}

            targets = get_target_keys(context,
                                      require_selected=props.affect_only_selected,
                                      visible_only=True,
                                      fallback_to_active=True,
                                      exclude_basis=True)
            if not targets:
                self.report({'INFO'}, "No selected shapekeys to mirror.")
                return {'CANCELLED'}

            values_cache = {k.name: float(getattr(k, "value", 0.0)) for k in ks}

            try:
                bpy.ops.object.mode_set(mode='OBJECT')
            except Exception:
                pass

            created = 0
            prefix = (self.key_name or "").strip()
            suffix = self.duplicate_suffix

            for src in targets:
                for k in ks:
                    try: k.value = 0.0
                    except: pass
                try:
                    src.value = 1.0
                except: pass

                bpy.ops.object.mode_set(mode='OBJECT')
                bpy.ops.object.shape_key_add(from_mix=True)

                new_idx = len(obj.data.shape_keys.key_blocks) - 1
                obj.active_shape_key_index = new_idx
                new_k = obj.data.shape_keys.key_blocks[new_idx]

                for k in ks:
                    try: k.value = 0.0
                    except: pass

                try:
                    bpy.ops.object.shape_key_mirror(use_topology=self.use_topology)
                except Exception as e:
                    self.report({'WARNING'}, f"Mirror failed on '{new_k.name}': {e}")
                
                if self.bake_vertex_groups and src.vertex_group:
                    vg = obj.vertex_groups.get(src.vertex_group)
                    if vg:
                        basis = obj.data.shape_keys.key_blocks[0]
                        for i in range(len(new_k.data)):
                            try:
                                weight = vg.weight(i)
                                if weight == 0:
                                    new_k.data[i].co = basis.data[i].co
                            except:
                                new_k.data[i].co = basis.data[i].co

                prefix = (self.key_name or "").strip()
                suffix = self.duplicate_suffix
                if not prefix and not suffix:
                    suffix = "_Mirror"
                new_k.name = f"{prefix}{src.name}{suffix}"
                it = ensure_item_by_name(new_k.name, create=True)
                self._move_key_after_source(obj, new_k.name, src.name)
                created += 1

                try:
                    new_k.slider_min = float(getattr(src, "slider_min", 0.0))
                    new_k.slider_max = float(getattr(src, "slider_max", 1.0))
                except:
                    pass

                for k in ks:
                    try: k.value = values_cache.get(k.name, 0.0)
                    except: pass

            try:
                bpy.context.view_layer.update()
                for win in bpy.context.window_manager.windows:
                    for area in win.screen.areas:
                        if area.type in {'PROPERTIES', 'VIEW_3D'}:
                            area.tag_redraw()
            except Exception:
                pass

            self.key_name = ""
            self.report({'INFO'}, f"Duplicated & mirrored {created} shapekey(s).")
            return {'FINISHED'}

        elif self.mode == 'SPLIT':
            obj = active_obj_mesh(context)
            if not obj:
                self.report({'WARNING'}, "Select a mesh object with shapekeys.")
                return {'CANCELLED'}

            ks = list(iter_keyblocks(obj))
            if not ks:
                self.report({'WARNING'}, "Object has no shapekeys to split.")
                return {'CANCELLED'}

            targets = get_target_keys(context,
                                      require_selected=props.affect_only_selected,
                                      visible_only=True,
                                      fallback_to_active=True,
                                      exclude_basis=True)
            if not targets:
                self.report({'WARNING'}, "Select one or more shapekeys (non-Basis) or set an active shapekey.")
                return {'CANCELLED'}

            values_cache = {k.name: float(getattr(k, "value", 0.0)) for k in ks}

            left_tok  = (self.split_left_token  or "").strip() or "_L"
            right_tok = (self.split_right_token or "").strip() or "_R"

            created = 0
            try:
                try:
                    bpy.ops.object.mode_set(mode='OBJECT')
                except Exception:
                    pass

                for src in targets:
                    for k in ks:
                        try: k.value = 0.0
                        except Exception: pass
                    try:
                        src.value = 1.0
                    except Exception:
                        pass

                    bpy.ops.object.shape_key_add(from_mix=True)
                    k_left = obj.data.shape_keys.key_blocks[-1]
                    obj.active_shape_key_index = len(obj.data.shape_keys.key_blocks) - 1

                    try:
                        k_left.value = 0.0
                    except Exception:
                        pass

                    bpy.ops.object.shape_key_add(from_mix=True)
                    k_right = obj.data.shape_keys.key_blocks[-1]
                    obj.active_shape_key_index = len(obj.data.shape_keys.key_blocks) - 1

                    k_left.name  = f"{src.name}{left_tok}"
                    k_right.name = f"{src.name}{right_tok}"

                    try:
                        for nk in (k_left, k_right):
                            nk.slider_min = float(getattr(src, "slider_min", 0.0))
                            nk.slider_max = float(getattr(src, "slider_max", 1.0))
                    except Exception:
                        pass

                    for k in iter_keyblocks(obj):
                        try: k.value = 0.0
                        except Exception: pass

                    changed_L = _sko_split_keyblock_half(
                        obj, k_left,
                        axis="X",
                        eps=max(0.0, self.split_eps),
                        keep_side='RIGHT',
                        use_median_plane=self.use_median_plane
                    )
                    changed_R = _sko_split_keyblock_half(
                        obj, k_right,
                        axis="X",
                        eps=max(0.0, self.split_eps),
                        keep_side='LEFT',
                        use_median_plane=self.use_median_plane
                    )

                    if changed_L == 0 or changed_R == 0:
                        self.report(
                            {'WARNING'},
                            f"Split '{src.name}' affected L:{changed_L} / R:{changed_R} vertices. "
                            f"Check threshold or the model’s symmetry vs X=0."
                        )

                    if self.bake_vertex_groups and src.vertex_group:
                        vg = obj.vertex_groups.get(src.vertex_group)
                        if vg:
                            basis = obj.data.shape_keys.key_blocks[0]
                            for key in [k_left, k_right]:
                                for i in range(len(key.data)):
                                    try:
                                        weight = vg.weight(i)
                                        if weight == 0:
                                            key.data[i].co = basis.data[i].co
                                    except:
                                        key.data[i].co = basis.data[i].co

                    it = ensure_item_by_name(k_left.name,  create=True)
                    it = ensure_item_by_name(k_right.name, create=True)

                    self._move_key_after_source(obj, k_left.name, src.name)
                    self._move_key_after_source(obj, k_right.name, k_left.name)

                    created += 2

                    if not self.keep_original:
                        try:
                            idx = list(obj.data.shape_keys.key_blocks).index(src)
                            obj.active_shape_key_index = idx
                            bpy.ops.object.shape_key_remove(all=False)
                        except Exception:
                            self.report({'WARNING'}, f"Could not remove original key '{src.name}'.")

                self.report({'INFO'}, f"Split {len(targets)} key(s) → created {created}.")
                return {'FINISHED'}

            finally:
                sk = getattr(getattr(obj.data, 'shape_keys', None), 'key_blocks', None)
                if sk:
                    for kb in sk:
                        try:
                            kb.value = float(values_cache.get(kb.name, 0.0))
                        except Exception:
                            pass
                try:
                    bpy.context.view_layer.update()
                    for win in bpy.context.window_manager.windows:
                        for area in win.screen.areas:
                            if area.type in {'PROPERTIES', 'VIEW_3D'}:
                                area.tag_redraw()
                except Exception:
                    pass

        elif self.mode == 'FACE_TEMPLATE':
            obj = active_obj_mesh(context)
            if not obj:
                self.report({'ERROR'}, "No mesh object selected.")
                return {'CANCELLED'}

            keys = _FACE_TEMPLATE_KEYS.get(self.face_template, [])
            if not keys:
                self.report({'ERROR'}, f"No keys defined for {self.face_template}.")
                return {'CANCELLED'}

            sk = getattr(obj.data, "shape_keys", None)
            if not sk:
                obj.shape_key_add(name="Basis")
                sk = obj.data.shape_keys

            kb = sk.key_blocks
            existing = set(kb.keys())

            created = 0
            skipped = 0

            separator_name = "-- FACE TRACKING --"
            if separator_name not in existing:
                try:
                    obj.shape_key_add(name=separator_name, from_mix=False)
                    created += 1
                    existing.add(separator_name)
                except Exception:
                    pass

            for name in keys:
                if name in existing:
                    if self.skip_existing:
                        skipped += 1
                        continue
                obj.shape_key_add(name=name, from_mix=False)
                created += 1

            self.report(
                {'INFO'},
                f"{self.face_template}: created {created} keys, skipped {skipped}."
            )
            return {'FINISHED'}
        
        # MIX_SELECTED
        ks = list(iter_keyblocks(obj))
        if not ks:
            self.report({'WARNING'}, "No shapekeys to combine.")
            return {'CANCELLED'}

        pool = filtered_keys(context, obj) if self.visible_only else ks

        values_cache = {k.name: float(getattr(k, "value", 0.0)) for k in ks}

        include = []
        for k in pool:
            if is_basis_key(obj, k):
                continue
            if not get_sel(k):
                continue
            if not self.include_zero and values_cache.get(k.name, 0.0) == 0.0:
                continue
            include.append(k)

        if not include:
            self.report({'INFO'}, "No selected (and eligible) shapekeys to combine.")
            return {'CANCELLED'}

        for k in ks:
            try:
                k.value = 0.0
            except Exception:
                pass

        for k in include:
            try:
                k.value = values_cache.get(k.name, 0.0)
            except Exception:
                pass

        try:
            bpy.ops.object.shape_key_add(from_mix=True)
        except Exception as e:
            for k in ks:
                try:
                    k.value = values_cache.get(k.name, 0.0)
                except Exception:
                    pass
            self.report({'ERROR'}, f"Could not create shapekey from selected mix: {e}")
            return {'CANCELLED'}

        new_key = _finalize_new_key()

        for k in ks:
            try:
                k.value = values_cache.get(k.name, 0.0)
            except Exception:
                pass

        self.report({'INFO'}, f"Created '{new_key.name if new_key else '(unknown)'}' from {len(include)} selected key(s).")
        self.key_name = ""
        return {'FINISHED'}

class SKO_OT_ShapeKeyDelete(bpy.types.Operator):
    bl_idname = "shapekey_organizer.shape_key_delete"
    bl_label = "Delete Shapekeys"
    bl_description = "Delete selected shapekeys; if none are selected, delete the active shapekey"
    bl_options = {'REGISTER', 'UNDO'}

    _target_names: list[str] = None
    _used_fallback: bool = False

    def _gather_targets(self, context):
        """Build target list and detect if we fell back to the active key."""
        obj = context.object
        if not obj or obj.type != 'MESH':
            return [], False

        pool = filtered_keys(context, obj)
        any_selected = any(get_sel(k) and not is_basis_key(obj, k) for k in pool)

        targets = get_target_keys(context,
                                  require_selected=True,
                                  visible_only=True,
                                  fallback_to_active=True,
                                  exclude_basis=True
        )
        names = [k.name for k in targets]
        used_fallback = (not any_selected) and (len(names) == 1)

        return names, used_fallback

    def invoke(self, context, event):
        names, used_fallback = self._gather_targets(context)
        if not names:
            self.report({'INFO'}, "No shapekeys to delete.")
            return {'CANCELLED'}

        self._target_names = names
        self._used_fallback = used_fallback
        return context.window_manager.invoke_props_dialog(self, width=360)

    def draw(self, context):
        layout = self.layout
        names = self._target_names or []

        if self._used_fallback and len(names) == 1:
            layout.label(text="Delete active shapekey?", icon='INFO')
            layout.label(text=names[0], icon='SHAPEKEY_DATA')
        else:
            layout.label(text=f"Delete {len(names)} shapekey(s)?", icon='INFO')
            for n in names[:6]:
                layout.label(text=n, icon='DOT')
            if len(names) > 6:
                layout.label(text="…")

    def execute(self, context):
        obj = context.object
        sk = getattr(getattr(obj.data, 'shape_keys', None), 'key_blocks', None)
        if not obj or not sk:
            return {'CANCELLED'}

        names = self._target_names
        if not names:
            names, _ = self._gather_targets(context)
            if not names:
                self.report({'INFO'}, "No shapekeys to delete.")
                return {'CANCELLED'}

        indices = []
        for n in names:
            kb = sk.get(n)
            if kb:
                idx = list(sk).index(kb)
                if idx > 0:
                    indices.append(idx)

        indices.sort(reverse=True)
        for idx in indices:
            obj.active_shape_key_index = idx
            try:
                bpy.ops.object.shape_key_remove(all=False)
            except Exception:
                pass

        self.report({'INFO'}, f"Deleted {len(indices)} shapekey(s).")
        return {'FINISHED'}


class SKO_OT_ToggleSelect(Operator):
    bl_idname = "shapekey_organizer.toggle_select"
    bl_label = "Toggle Select"
    bl_description = "Click to toggle; Shift-click to select a range between the anchor and this item"
    bl_options = {'INTERNAL', 'UNDO'}

    key_name: StringProperty(name="Key Name")
    range_mode: BoolProperty(options={'HIDDEN'}, default=False)

    def invoke(self, context, event):
        self.range_mode = bool(getattr(event, "shift", False))
        return self.execute(context)

    def execute(self, context):
        obj = context.object
        if not obj or obj.type != 'MESH':
            self.report({'WARNING'}, "Select a mesh object with shapekeys.")
            return {'CANCELLED'}

        ks = getattr(getattr(obj.data, 'shape_keys', None), 'key_blocks', None)
        if not ks:
            return {'CANCELLED'}

        props = context.scene.shapekey_organizer

        idx_of = {k.name: i for i, k in enumerate(ks)}
        if self.key_name not in idx_of:
            return {'CANCELLED'}
        current_idx = idx_of[self.key_name]

        visible_names = [k.name for k in filtered_keys(context, obj)]
        visible_set = {idx_of[n] for n in visible_names if n in idx_of}

        if self.range_mode and props.anchor_index >= 0 and props.anchor_index in visible_set and current_idx in visible_set:
            a, b = sorted([props.anchor_index, current_idx])

            new_state = not get_sel(ks[current_idx])

            for i in range(a, b + 1):
                if i in visible_set:
                    set_sel(ks[i], new_state)
        else:
            set_sel(ks[current_idx], not get_sel(ks[current_idx]))
            props.anchor_index = current_idx

        return {'FINISHED'}


class SKO_OT_SyncState(Operator):
    bl_idname = "shapekey_organizer.sync_state"
    bl_label = "Refresh"
    bl_description = "Scan current object and create state entries for all shapekeys (safe)"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        obj = active_obj_mesh(context)
        if not obj:
            self.report({'WARNING'}, "Select a mesh object with shapekeys.")
            return {'CANCELLED'}
        created = 0
        for k in iter_keyblocks(obj):
            if not find_item_by_name(k.name):
                it = ensure_item_by_name(k.name, create=True)
                if it:
                    created += 1
        self.report({'INFO'}, f"State synced for {created} keys.")
        return {'FINISHED'}


class SKO_OT_SelectAll(Operator):
    bl_idname = "shapekey_organizer.select_all"
    bl_label = "All"
    bl_description = "Select all currently visible (filtered) shapekeys (ignores Basis)"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        obj = active_obj_mesh(context)
        if not obj:
            self.report({'WARNING'}, "Select a mesh object with shapekeys.")
            return {'CANCELLED'}
        for k in filtered_keys(context, obj):
            if is_basis_key(obj, k):
                continue
            set_sel(k, True)
        return {'FINISHED'}


class SKO_OT_SelectNone(Operator):
    bl_idname = "shapekey_organizer.select_none"
    bl_label = "None"
    bl_description = "Clear selection for all currently visible (filtered) shapekeys"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        obj = active_obj_mesh(context)
        if not obj:
            self.report({'WARNING'}, "Select a mesh object with shapekeys.")
            return {'CANCELLED'}
        for k in filtered_keys(context, obj):
            set_sel(k, False)
        return {'FINISHED'}


class SKO_OT_SelectInvert(Operator):
    bl_idname = "shapekey_organizer.select_invert"
    bl_label = "Invert"
    bl_description = "Invert selection for all currently visible (filtered) shapekeys (ignores Basis)"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        obj = active_obj_mesh(context)
        if not obj:
            self.report({'WARNING'}, "Select a mesh object with shapekeys.")
            return {'CANCELLED'}
        for k in filtered_keys(context, obj):
            if is_basis_key(obj, k):
                continue
            set_sel(k, not get_sel(k))
        return {'FINISHED'}


class SKO_OT_AssignGroup(Operator):
    bl_idname = "shapekey_organizer.assign_group"
    bl_label = "Assign Group"
    bl_description = "Assign the current Group field value to selected shapekeys"
    bl_options = {'REGISTER', 'UNDO'}

    group: StringProperty(name="Group", description="Group name to assign to selected keys")

    def execute(self, context):
        obj = active_obj_mesh(context)
        if not obj:
            self.report({'WARNING'}, "Select a mesh object with shapekeys.")
            return {'CANCELLED'}

        props = context.scene.shapekey_organizer

        gname = (self.group or "").strip() or (props.group_search or "").strip()
        if not gname:
            self.report({'WARNING'}, "Enter a group name first.")
            return {'CANCELLED'}

        all_keys = list(iter_keyblocks(obj))
        selected_targets = [k for k in all_keys if get_sel(k) and not is_basis_key(obj, k)]

        if not selected_targets:
            ak = getattr(obj, "active_shape_key", None)
            if ak and not is_basis_key(obj, ak):
                targets = [ak]
            else:
                targets = []
        else:
            targets = selected_targets

        if not targets:
            self.report({'INFO'}, "No shapekeys to assign (Basis is ignored).")
            return {'CANCELLED'}

        for k in targets:
            set_group(k, gname)

        ensure_group(context, gname)

        try:
            bpy.context.view_layer.update()
            for win in bpy.context.window_manager.windows:
                for area in win.screen.areas:
                    if area.type in {'PROPERTIES', 'VIEW_3D'}:
                        area.tag_redraw()
        except Exception:
            pass

        self.report({'INFO'}, f"Assigned group '{gname}' to {len(targets)} key(s).")
        return {'FINISHED'}


class SKO_OT_ClearGroup(Operator):
    bl_idname = "shapekey_organizer.clear_group"
    bl_label = "Clear Group"
    bl_description = "Clear the group tag from selected shapekeys"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        obj = active_obj_mesh(context)
        if not obj:
            self.report({'WARNING'}, "Select a mesh object with shapekeys.")
            return {'CANCELLED'}
        count = 0
        for k in iter_keyblocks(obj):
            if get_sel(k):
                set_group(k, "")
                count += 1
        self.report({'INFO'}, f"Cleared group on {count} keys.")
        return {'FINISHED'}


class SKO_OT_PrefixSuffix(Operator):
    bl_idname = "shapekey_organizer.add_prefix_suffix"
    bl_label = "Apply Prefix/Suffix"
    bl_description = "Add prefix and/or suffix to each affected shapekey name"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        obj = active_obj_mesh(context)
        if not obj:
            self.report({'WARNING'}, "Select a mesh object with shapekeys.")
            return {'CANCELLED'}

        props = context.scene.shapekey_organizer
        pre, suf = props.prefix, props.suffix
        if not pre and not suf:
            self.report({'WARNING'}, "Nothing to add (enter a prefix and/or suffix).")
            return {'CANCELLED'}

        targets = get_target_keys(context,
                                  require_selected=props.affect_only_selected,
                                  visible_only=True,
                                  fallback_to_active=True,
                                  exclude_basis=True
        )
        if not targets:
            self.report({'INFO'}, "No shapekeys to rename.")
            return {'CANCELLED'}

        count = 0
        for k in targets:
            it = ensure_item_by_name(k.name, create=True)
            new_name = f"{pre}{k.name}{suf}"
            k.name = new_name
            if it:
                it.key_name = new_name
            count += 1

        self.report({'INFO'}, f"Renamed {count} key(s).")
        return {'FINISHED'}


class SKO_OT_FindReplace(Operator):
    bl_idname = "shapekey_organizer.find_replace"
    bl_label = "Find & Replace"
    bl_description = "Find text in names and replace it for each affected shapekey (case-insensitive by default)"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        obj = active_obj_mesh(context)
        if not obj:
            self.report({'WARNING'}, "Select a mesh object with shapekeys.")
            return {'CANCELLED'}
        props = context.scene.shapekey_organizer
        find = props.find
        repl = props.replace
        if not find:
            self.report({'WARNING'}, "Enter text to find.")
            return {'CANCELLED'}

        case_sensitive = props.find_case_sensitive
        count = 0
        if case_sensitive:
            for k in iter_keyblocks(obj):
                if props.affect_only_selected and not get_sel(k):
                    continue
                if find in k.name:
                    it = ensure_item_by_name(k.name, create=True)
                    new_name = k.name.replace(find, repl)
                    k.name = new_name
                    if it:
                        it.key_name = k.name
                    count += 1
        else:
            pattern = re.compile(re.escape(find), re.IGNORECASE)
            for k in iter_keyblocks(obj):
                if props.affect_only_selected and not get_sel(k):
                    continue
                if pattern.search(k.name):
                    it = ensure_item_by_name(k.name, create=True)
                    new_name = pattern.sub(repl, k.name)
                    k.name = new_name
                    if it:
                        it.key_name = k.name
                    count += 1

        self.report({'INFO'}, f"Renamed {count} keys.")
        return {'FINISHED'}


class SKO_OT_AutoNumber(Operator):
    bl_idname = "shapekey_organizer.auto_number"
    bl_label = "Auto-Number"
    bl_description = "Append an increasing number to each affected shapekey name"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        obj = active_obj_mesh(context)
        if not obj:
            self.report({'WARNING'}, "Select a mesh object with shapekeys.")
            return {'CANCELLED'}
        props = context.scene.shapekey_organizer
        i = props.auto_number_start
        pad = props.auto_number_pad
        count = 0
        for k in iter_keyblocks(obj):
            if is_basis_key(obj, k):
                continue
            if props.affect_only_selected and not get_sel(k):
                continue
            it = ensure_item_by_name(k.name, create=True)
            new_name = f"{k.name} {str(i).zfill(pad)}"
            k.name = new_name
            it.key_name = new_name
            i += 1
            count += 1
        self.report({'INFO'}, f"Auto-numbered {count} keys.")
        return {'FINISHED'}


class SKO_OT_Sort(Operator):
    bl_idname = "shapekey_organizer.sort"
    bl_label = "Sort Selected"
    bl_description = ("Sort visible keys (or only selected if enabled). "
                      "Modes: A→Z (All), Z→A (All), or Group List → Name (ungrouped last). "
                      "Basis stays at the top.")
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        obj = context.object
        if not obj or obj.type != 'MESH':
            self.report({'WARNING'}, "Select a mesh object with shapekeys.")
            return {'CANCELLED'}

        ks = getattr(getattr(obj.data, 'shape_keys', None), 'key_blocks', None)
        if not ks:
            self.report({'INFO'}, "No shapekeys found.")
            return {'CANCELLED'}

        props = context.scene.shapekey_organizer

        visible = filtered_keys(context, obj)

        targets = [k for k in visible if get_sel(k)] if props.affect_only_selected else list(visible)
        if not targets:
            self.report({'INFO'}, "Nothing to sort (check filters/selection).")
            return {'CANCELLED'}

        mode = props.sort_mode

        if mode in {'NAME_ASC', 'NAME_DESC'}:
            reverse = (mode == 'NAME_DESC')
            ordered = sorted(targets, key=lambda k: k.name.lower(), reverse=reverse)
            order_name = "Name A→Z" if not reverse else "Name Z→A"
        else:
            glist = [g.name for g in all_groups(context)]
            gprio = {name: i for i, name in enumerate(glist)}

            def sort_key(k):
                gname = get_group(k)
                gindex = gprio.get(gname, 999999)  # ungrouped last
                return (gindex, k.name.lower())

            ordered = sorted(targets, key=sort_key)
            order_name = "Group List → Name"

        def index_of(name: str) -> int:
            for i, kb in enumerate(obj.data.shape_keys.key_blocks):
                if kb.name == name:
                    return i
            return -1

        if context.mode != 'OBJECT':
            try:
                bpy.ops.object.mode_set(mode='OBJECT')
            except Exception as e:
                self.report({'ERROR'}, f"Cannot sort in current mode: {e}")
                return {'CANCELLED'}

        for k in reversed(ordered):
            i = index_of(k.name)
            if i < 0:
                continue
            obj.active_shape_key_index = i
            bpy.ops.object.shape_key_move(type='TOP')
            while obj.active_shape_key_index == 0:
                bpy.ops.object.shape_key_move(type='DOWN')

        self.report({'INFO'}, f"Sorted {len(ordered)} keys: {order_name}.")
        return {'FINISHED'}



class SKO_OT_MoveSelected(Operator):
    bl_idname = "shapekey_organizer.move_selected"
    bl_label = "Move Selected"
    bl_description = "Move selected keys within the stack. 'Top' always means just under Basis"
    bl_options = {'REGISTER', 'UNDO'}

    direction: EnumProperty(
        name="Direction",
        description="Where to move the selected keys",
        items=[('TOP', 'Top', ''), ('UP', 'Up', ''), ('DOWN', 'Down', ''), ('BOTTOM', 'Bottom', '')],
        default='TOP'
    )

    def execute(self, context):
        obj = active_obj_mesh(context)
        if not obj:
            self.report({'WARNING'}, "Select a mesh object with shapekeys.")
            return {'CANCELLED'}

        targets = get_target_keys(context,
                                  require_selected=True,
                                  visible_only=True,
                                  fallback_to_active=True,
                                  exclude_basis=True)
        if not targets:
            self.report({'INFO'}, "No keys to move.")
            return {'CANCELLED'}

        ks = list(iter_keyblocks(obj))
        name_to_idx = {k.name: i for i, k in enumerate(ks)}
        idxs = [name_to_idx[k.name] for k in targets if k.name in name_to_idx]

        if self.direction in {'TOP', 'UP'}:
            order = sorted(idxs)
        else:
            order = sorted(idxs, reverse=True)

        target_names = [ks[i].name for i in order]

        for name in target_names:
            current_idx = -1
            for i, k in enumerate(obj.data.shape_keys.key_blocks):
                if k.name == name:
                    current_idx = i
                    break

            if current_idx < 0:
                continue

            obj.active_shape_key_index = current_idx

            if self.direction == 'TOP':
                move_active_to_top_below_basis(obj)
            else:
                bpy.ops.object.shape_key_move(type=self.direction)
                if self.direction == 'UP':
                    _ensure_active_not_basis(obj)

        self.report({'INFO'}, f"Moved {len(order)} keys {self.direction.lower()}.")
        return {'FINISHED'}


class SKO_OT_ToggleMute(Operator):
    bl_idname = "shapekey_organizer.toggle_mute"
    bl_label = "Mute/Unmute"
    bl_description = "Mute, unmute, or toggle mute state on selected (or visible) keys"
    bl_options = {'REGISTER', 'UNDO'}

    state: EnumProperty(
        name="State",
        description="How to change the mute flag",
        items=[('ON','On','Mute selected keys'),('OFF','Off','Unmute selected keys'),('TOGGLE','Toggle','Toggle the mute flag')],
        default='TOGGLE')

    def execute(self, context):
        obj = active_obj_mesh(context)
        if not obj:
            self.report({'WARNING'}, "Select a mesh object with shapekeys.")
            return {'CANCELLED'}
        count = 0
        for k in iter_keyblocks(obj):
            if not get_sel(k):
                continue
            if self.state == 'TOGGLE':
                k.mute = not k.mute
            elif self.state == 'ON':
                k.mute = True
            else:
                k.mute = False
            count += 1
        self.report({'INFO'}, f"Updated mute on {count} keys.")
        return {'FINISHED'}


class SKO_OT_SetSliderRange(Operator):
    bl_idname = "shapekey_organizer.set_slider_range"
    bl_label = "Set Slider Range"
    bl_description = "Apply slider min/max to affected shapekeys"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        obj = active_obj_mesh(context)
        if not obj:
            self.report({'WARNING'}, "Select a mesh object with shapekeys.")
            return {'CANCELLED'}
        props = context.scene.shapekey_organizer

        min_v = max(0.0, min(1.0, float(props.slider_min)))
        max_v = max(0.0, min(1.0, float(props.slider_max)))

        if min_v > max_v:
            min_v, max_v = max_v, min_v

        if abs(max_v - min_v) < 1e-9:
            eps = 1e-4
            if min_v <= 0.0:
                max_v = min(min_v + eps, 1.0)
            elif max_v >= 1.0:
                min_v = max(max_v - eps, 0.0)
            else:
                half = eps * 0.5
                min_v = max(0.0, min_v - half)
                max_v = min(1.0, max_v + half)

        targets = get_target_keys(context,
                                  require_selected=props.affect_only_selected,
                                  visible_only=True,
                                  fallback_to_active=True,
                                  exclude_basis=True)
        if not targets:
            self.report({'INFO'}, "No visible shapekeys to update.")
            return {'CANCELLED'}

        count = 0
        for k in targets:
            try:
                k.slider_min = min_v
                k.slider_max = max_v
            except Exception:
                continue
            try:
                if k.value < min_v:
                    k.value = min_v
                elif k.value > max_v:
                    k.value = max_v
            except Exception:
                pass
            count += 1
        self.report({'INFO'}, f"Updated slider ranges on {count} keys.")
        return {'FINISHED'}


class SKO_OT_ResetValues(Operator):
    bl_idname = "shapekey_organizer.reset_values"
    bl_label = "Reset Values to 0"
    bl_description = "Reset slider range and set value = 0.0 for affected shapekeys"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        obj = active_obj_mesh(context)
        if not obj:
            self.report({'WARNING'}, "Select a mesh object with shapekeys.")
            return {'CANCELLED'}
        props = context.scene.shapekey_organizer

        targets = get_target_keys(context,
                                  require_selected=props.affect_only_selected,
                                  visible_only=True,
                                  fallback_to_active=True,
                                  exclude_basis=True)
        if not targets:
            self.report({'INFO'}, "No visible shapekeys to reset.")
            return {'CANCELLED'}

        default_min, default_max = 0.0, 1.0
        ranges_reset = 0
        values_reset = 0

        for k in targets:
            try:
                k.slider_min = default_min
                k.slider_max = default_max
                ranges_reset += 1
            except Exception:
                pass

            if is_basis_key(obj, k):
                continue
            try:
                k.value = 0.0
                values_reset += 1
            except Exception:
                pass

        props.slider_min = 0.0
        props.slider_max = 1.0

        try:
            for win in bpy.context.window_manager.windows:
                for area in win.screen.areas:
                    if area.type == 'PROPERTIES':
                        area.tag_redraw()
        except Exception:
            pass

        self.report({'INFO'}, f"Reset ranges on {ranges_reset} keys and values on {values_reset} keys.")
        return {'FINISHED'}


class SKO_OT_SelectEmptyShapeKeys(Operator):
    bl_idname = "shapekey_organizer.select_empty"
    bl_label = "Select Empty Shapekeys"
    bl_description = "Select shapekeys with no vertex deformation based on threshold"
    bl_options = {'REGISTER', 'UNDO'}
    
    threshold: FloatProperty(
        name="Threshold",
        description="Maximum vertex delta to consider a shapekey 'empty'",
        default=0.00001,
        min=0.0,
        soft_max=0.01,
        precision=6
    )
    
    only_visible: BoolProperty(
        name="Only Visible",
        description="Only check visible (filtered) shapekeys",
        default=True
    )
    
    deselect_others: BoolProperty(
        name="Deselect Others",
        description="Deselect all other shapekeys before selecting empty ones",
        default=False
    )

    scan_done: BoolProperty(default=False, options={'HIDDEN', 'SKIP_SAVE'})
    scan_obj: PointerProperty(type=bpy.types.Object, options={'HIDDEN', 'SKIP_SAVE'})
    
    def ensure_scan(self, context):
        """Compute max_delta for all non-basis shapekeys once with progress."""
        if not hasattr(self, 'all_keys_data'):
            self.all_keys_data = []
        
        if getattr(self, 'scan_done', False) and getattr(self, 'scan_obj', None) is context.object:
            return
        
        obj = active_obj_mesh(context)
        self.scan_obj = obj
        self.scan_done = True
        
        if not obj:
            return
        
        sk = getattr(obj.data, 'shape_keys', None)
        if not sk or len(sk.key_blocks) <= 1:
            return
        
        keys_to_scan = [k for k in iter_keyblocks(obj) if not is_basis_key(obj, k)]

        if not keys_to_scan:
            return

        wm = context.window_manager
        wm.progress_begin(0, len(keys_to_scan))
        sko_set_status_text(context, "Scanning shapekeys...")
        
        data = []
        try:
            for i, k in enumerate(keys_to_scan):
                wm.progress_update(i)
                sko_set_status_text(context, f"Scanning {k.name} ({i+1}/{len(keys_to_scan)})...")
                
                max_d = shapekey_max_delta(obj, k)
                data.append((k, max_d))
        finally:
            wm.progress_end()
            sko_set_status_text(context, None)
        
        self.all_keys_data = data
    
    def empty_keys_for_threshold(self, threshold):
        """Keys whose max_delta <= threshold (using cached scan)."""
        if not hasattr(self, 'all_keys_data'):
            return []
        return [k for k, d in self.all_keys_data if d <= threshold]
    
    def filter_for_selection(self, context, empty_keys):
        """From the threshold-based empty keys, return those that match visibility filter."""
        obj = active_obj_mesh(context)
        if not obj:
            return []
        
        if self.only_visible:
            visible_pool = set(filtered_keys(context, obj))
        else:
            visible_pool = set(iter_keyblocks(obj))
        
        out = []
        for k in empty_keys:
            if self.only_visible and k not in visible_pool:
                continue
            out.append(k)
        
        return out
    
    def invoke(self, context, event):
        self.scan_done = False
        self.scan_obj = None
        self.all_keys_data = []
        self.ensure_scan(context)
        return context.window_manager.invoke_props_dialog(self)
    
    def draw(self, context):
        layout = self.layout
        col = layout.column(align=True)
        
        obj = active_obj_mesh(context)
        if not obj:
            col.label(text="No active mesh object.", icon='ERROR')
            return
        
        self.ensure_scan(context)

        col.prop(self, "threshold")
        row = col.row(align=True)
        row.prop(self, "only_visible")
        row.prop(self, "deselect_others")

        SCAN_EPS = 1e-6
        if not hasattr(self, 'all_keys_data'):
            return
        
        truly_empty = [k for k, d in self.all_keys_data if d <= SCAN_EPS]
        
        if not truly_empty:
            box = layout.box()
            box.label(text="No empty shapekeys found on this object", icon='INFO')
            return

        empty_all = self.empty_keys_for_threshold(self.threshold)
        to_select = self.filter_for_selection(context, empty_all)
        
        box = layout.box()
        box.label(text=f"Will select: {len(to_select)} shapekey(s)", icon='CHECKMARK')

        if to_select:
            col = box.column(align=True)
            col.scale_y = 0.8
            for k in to_select[:10]:
                delta = next((d for key, d in self.all_keys_data if key == k), 0)
                col.label(text=f"{k.name}")
            if len(to_select) > 10:
                col.label(text=f"  ... and {len(to_select) - 10} more")
    
    def execute(self, context):
        self.ensure_scan(context)
        
        empty_all = self.empty_keys_for_threshold(self.threshold)
        if not empty_all:
            self.report({'INFO'}, "No empty shapekeys found with current threshold")
            return {'CANCELLED'}
        
        to_select = self.filter_for_selection(context, empty_all)
        if not to_select:
            self.report({'INFO'}, "No empty shapekeys match current filters")
            return {'CANCELLED'}
        
        obj = active_obj_mesh(context)
        if not obj:
            return {'CANCELLED'}

        if self.deselect_others:
            for k in iter_keyblocks(obj):
                set_sel(k, False)

        for k in to_select:
            set_sel(k, True)

        try:
            bpy.context.view_layer.update()
            for win in bpy.context.window_manager.windows:
                for area in win.screen.areas:
                    if area.type in {'PROPERTIES', 'VIEW_3D'}:
                        area.tag_redraw()
        except Exception:
            pass
        
        self.report({'INFO'}, f"Selected {len(to_select)} empty shapekeys")
        return {'FINISHED'}


class SKO_OT_TransferSelectedShapeKeys(Operator):
    bl_idname = "shapekey_organizer.transfer_selected"
    bl_label = "Transfer Selected Shape Keys"
    bl_description = (
        "Transfer the selected shapekeys from the active mesh to the target object\n"
        "using the chosen transfer mode"
    )
    bl_options = {'UNDO'}

    def _get_source_target(self, context):
        src = active_obj_mesh(context)
        props = context.scene.shapekey_organizer
        dst = props.transfer_target
        if dst is not None and dst.type != 'MESH':
            dst = None
        return src, dst

    def _get_selected_keys(self, context, src):
        keys = []
        for k in filtered_keys(context, src):
            if get_sel(k):
                keys.append(k)
        return keys

    def validate_source_keys(self, src, keys):
        """Filter out keys that are effectively empty (no deformation)"""
        valid = []
        for k in keys:
            max_delta = shapekey_max_delta(src, k)
            if max_delta < 1e-6:
                continue
            valid.append(k)
        return valid

    def direct_copy(self, src, dst, key_src, key_dst):
        """
        Direct vertex-to-vertex copy. Requires identical topology.
        """
        kd_src = key_src.data
        kd_dst = key_dst.data

        n = len(kd_src)
        if n != len(kd_dst):
            return 0, n

        for i in range(n):
            kd_dst[i].co = kd_src[i].co.copy()

        return n, 0

    def nearest_vertex(self, src, dst, key_src, key_dst, tree, max_distance):
        """
        Transfer by finding the nearest vertex on the source mesh for each destination vertex.
        Uses world-space positions.
        """
        sk_src = src.data.shape_keys
        basis_src = sk_src.key_blocks[0]
        sk_dst = dst.data.shape_keys
        basis_dst = sk_dst.key_blocks[0]

        kd_src = key_src.data
        bd_src = basis_src.data
        kd_dst = key_dst.data
        bd_dst = basis_dst.data

        mw_src = src.matrix_world
        mw_dst = dst.matrix_world
        mw_dst_inv = mw_dst.inverted()

        n_dst = len(dst.data.vertices)
        transferred = 0
        skipped = 0

        for i in range(n_dst):
            pos_world_dst = mw_dst @ bd_dst[i].co

            nearest_co, nearest_idx, dist = tree.find(pos_world_dst)

            if max_distance > 0.0 and dist > max_distance:
                kd_dst[i].co = bd_dst[i].co
                skipped += 1
                continue

            if nearest_idx is None or nearest_idx < 0:
                kd_dst[i].co = bd_dst[i].co
                skipped += 1
                continue

            delta_local = kd_src[nearest_idx].co - bd_src[nearest_idx].co

            delta_world = mw_src.to_3x3() @ delta_local

            basis_world_dst = mw_dst @ bd_dst[i].co
            new_world = basis_world_dst + delta_world

            kd_dst[i].co = mw_dst_inv @ new_world
            transferred += 1

        return transferred, skipped


    def nearest_barycentric(self, src, dst, key_src, key_dst, bvh, triangles, basis_world_src, max_distance):
        """
        Transfer by finding the nearest point on the source surface, then use barycentric
        interpolation within the triangle.
        """
        sk_src = src.data.shape_keys
        basis_src = sk_src.key_blocks[0]
        sk_dst = dst.data.shape_keys
        basis_dst = sk_dst.key_blocks[0]

        kd_src = key_src.data
        bd_src = basis_src.data
        kd_dst = key_dst.data
        bd_dst = basis_dst.data

        mw_src = src.matrix_world
        mw_dst = dst.matrix_world
        mw_dst_inv = mw_dst.inverted()

        n_dst = len(dst.data.vertices)
        transferred = 0
        skipped = 0

        for i in range(n_dst):
            pos_world_dst = mw_dst @ bd_dst[i].co

            hit_loc, hit_normal, tri_idx, dist = bvh.find_nearest(pos_world_dst)

            if hit_loc is None or tri_idx is None or tri_idx < 0:
                kd_dst[i].co = bd_dst[i].co
                skipped += 1
                continue

            if max_distance > 0.0 and dist > max_distance:
                kd_dst[i].co = bd_dst[i].co
                skipped += 1
                continue

            tri = triangles[tri_idx]
            v0_idx, v1_idx, v2_idx = tri[0], tri[1], tri[2]

            a_world = basis_world_src[v0_idx]
            b_world = basis_world_src[v1_idx]
            c_world = basis_world_src[v2_idx]

            bary = barycentric_coords(hit_loc, a_world, b_world, c_world)

            if bary is None:
                kd_dst[i].co = bd_dst[i].co
                skipped += 1
                continue

            u, v, w = bary

            a_deformed = kd_src[v0_idx].co
            b_deformed = kd_src[v1_idx].co
            c_deformed = kd_src[v2_idx].co

            a_basis = bd_src[v0_idx].co
            b_basis = bd_src[v1_idx].co
            c_basis = bd_src[v2_idx].co

            basis_interp_local = u * a_basis + v * b_basis + w * c_basis

            deformed_interp_local = u * a_deformed + v * b_deformed + w * c_deformed

            delta_local = deformed_interp_local - basis_interp_local

            delta_world = mw_src.to_3x3() @ delta_local

            basis_world_dst = mw_dst @ bd_dst[i].co
            new_world = basis_world_dst + delta_world

            kd_dst[i].co = mw_dst_inv @ new_world
            transferred += 1

        return transferred, skipped


    def raycast(self, src, dst, key_src, key_dst, bvh, triangles, basis_world_src, max_distance):
        """
        Transfer shapekey by raycasting along target vertex normals to find corresponding
        source surface points, then use barycentric interpolation.
        """
        sk_src = src.data.shape_keys
        basis_src = sk_src.key_blocks[0]
        sk_dst = dst.data.shape_keys
        basis_dst = sk_dst.key_blocks[0]

        kd_src = key_src.data
        bd_src = basis_src.data
        kd_dst = key_dst.data
        bd_dst = basis_dst.data

        mw_src = src.matrix_world
        mw_dst = dst.matrix_world
        mw_dst_inv = mw_dst.inverted()

        n_dst = len(dst.data.vertices)
        transferred = 0
        skipped = 0

        for i in range(n_dst):
            v_dst = dst.data.vertices[i]

            origin_world = mw_dst @ v_dst.co
            normal_world = (mw_dst.to_3x3() @ v_dst.normal).normalized()

            hit_loc, hit_normal, tri_idx, dist = bvh.ray_cast(origin_world, normal_world)

            if hit_loc is None:
                hit_loc, hit_normal, tri_idx, dist = bvh.ray_cast(origin_world, -normal_world)

            if hit_loc is None:
                hit_loc, hit_normal, tri_idx, dist = bvh.find_nearest(origin_world)

            if hit_loc is None or tri_idx is None or tri_idx < 0:
                kd_dst[i].co = bd_dst[i].co
                skipped += 1
                continue

            if max_distance > 0.0 and dist > max_distance:
                kd_dst[i].co = bd_dst[i].co
                skipped += 1
                continue

            tri = triangles[tri_idx]
            v0_idx, v1_idx, v2_idx = tri[0], tri[1], tri[2]

            a_world = basis_world_src[v0_idx]
            b_world = basis_world_src[v1_idx]
            c_world = basis_world_src[v2_idx]

            bary = barycentric_coords(hit_loc, a_world, b_world, c_world)

            if bary is None:
                kd_dst[i].co = bd_dst[i].co
                skipped += 1
                continue

            u, v, w = bary

            a_deformed = kd_src[v0_idx].co
            b_deformed = kd_src[v1_idx].co
            c_deformed = kd_src[v2_idx].co

            a_basis = bd_src[v0_idx].co
            b_basis = bd_src[v1_idx].co
            c_basis = bd_src[v2_idx].co

            basis_interp_local = u * a_basis + v * b_basis + w * c_basis

            deformed_interp_local = u * a_deformed + v * b_deformed + w * c_deformed

            delta_local = deformed_interp_local - basis_interp_local

            delta_world = mw_src.to_3x3() @ delta_local

            basis_world_dst = mw_dst @ bd_dst[i].co
            new_world = basis_world_dst + delta_world

            kd_dst[i].co = mw_dst_inv @ new_world
            transferred += 1

        return transferred, skipped

    def execute(self, context):
        props = context.scene.shapekey_organizer
        src, dst = self._get_source_target(context)

        if not src or not dst:
            self.report({'ERROR'}, "Source (active) and target mesh required")
            return {'CANCELLED'}

        if src == dst:
            self.report({'WARNING'}, "Source and target cannot be the same object")
            return {'CANCELLED'}

        keys_to_transfer = self._get_selected_keys(context, src)
        if not keys_to_transfer:
            self.report({'INFO'}, "No shapekeys selected in organizer")
            return {'CANCELLED'}

        keys_to_transfer = self.validate_source_keys(src, keys_to_transfer)
        if not keys_to_transfer:
            self.report({'WARNING'}, "All selected shapekeys are empty (no deformation)")
            return {'CANCELLED'}

        sk_src = getattr(src.data, "shape_keys", None)
        if not sk_src:
            self.report({'ERROR'}, "Source object has no shapekeys")
            return {'CANCELLED'}

        sk_dst = getattr(dst.data, "shape_keys", None)
        if not sk_dst:
            dst.shape_key_add(name="Basis")
            sk_dst = dst.data.shape_keys

        basis_src = sk_src.key_blocks[0]
        basis_dst = sk_dst.key_blocks[0]

        same_count = (len(src.data.vertices) == len(dst.data.vertices))
        if props.transfer_mode == 'MATCH_TOPOLOGY' and not same_count:
            self.report({'ERROR'}, "Match Topology mode requires identical vertex counts")
            return {'CANCELLED'}

        max_distance = 0.0
        if props.transfer_mode != 'MATCH_TOPOLOGY' and props.transfer_distance_ratio > 0.0:
            src_size = obj_world_size(src)
            dst_size = obj_world_size(dst)
            avg_size = (src_size + dst_size) / 2.0
            max_distance = avg_size * props.transfer_distance_ratio


        tree_world = None
        if props.transfer_mode == 'NEAREST_VERTEX':
            try:
                mw_src = src.matrix_world
                sk = src.data.shape_keys
                basis = sk.key_blocks[0] if sk and sk.key_blocks else None
                if not basis:
                    self.report({'ERROR'}, "Source has no Basis shapekey")
                    return {'CANCELLED'}

                n = len(basis.data)
                tree_world = KDTree(n)
                for i, kd in enumerate(basis.data):
                    tree_world.insert(mw_src @ kd.co, i)
                tree_world.balance()
            except Exception as e:
                self.report({'ERROR'}, f"Failed to build KDTree: {e}")
                return {'CANCELLED'}

        bvh = None
        triangles = None
        basis_world_src = None
        if props.transfer_mode in {'NEAREST_BARYCENTRIC', 'RAYCAST'}:
            try:
                bvh, triangles, basis_world_src = build_basis_bvh(src)
                if bvh is None:
                    self.report({'ERROR'}, "Failed to build BVH for source object (no triangles found)")
                    return {'CANCELLED'}
            except Exception as e:
                self.report({'ERROR'}, f"Failed to build BVH: {e}")
                return {'CANCELLED'}


        created = 0
        overwritten = 0
        skipped = 0
        wm = context.window_manager
        total = len(keys_to_transfer)
        wm.progress_begin(0, total)
        sko_set_status_text(context, "Transferring shapekeys...")

        try:
            for i, key_src in enumerate(keys_to_transfer):
                wm.progress_update(i)
                sko_set_status_text(context, f"Transferring {key_src.name} ({i+1}/{total})...")

                if key_src == basis_src:
                    continue

                key_dst = sk_dst.key_blocks.get(key_src.name)

                if key_dst is None:
                    if not props.transfer_create_missing:
                        skipped += 1
                        continue
                    key_dst = dst.shape_key_add(name=key_src.name, from_mix=False)
                    created += 1
                else:
                    if not props.transfer_overwrite_existing:
                        skipped += 1
                        continue
                    overwritten += 1

                mode = props.transfer_mode
                transferred = 0
                method_skipped = 0

                if mode == 'MATCH_TOPOLOGY':
                    transferred, method_skipped = self.direct_copy(src, dst, key_src, key_dst)
                elif mode == 'NEAREST_VERTEX':
                    transferred, method_skipped = self.nearest_vertex(src, dst, key_src, key_dst, tree_world, max_distance)
                elif mode == 'NEAREST_BARYCENTRIC':
                    transferred, method_skipped = self.nearest_barycentric(src, dst, key_src, key_dst, bvh, triangles, basis_world_src, max_distance)
                elif mode == 'RAYCAST':
                    transferred, method_skipped = self.raycast(src, dst, key_src, key_dst, bvh, triangles, basis_world_src, max_distance)

                if props.transfer_copy_settings:
                    for attr in ['value', 'slider_min', 'slider_max', 'mute', 'interpolation']:
                        if hasattr(key_src, attr):
                            setattr(key_dst, attr, getattr(key_src, attr))
                    for attr in ['vertex_group', 'range_min', 'range_max']:
                        if hasattr(key_src, attr):
                            setattr(key_dst, attr, getattr(key_src, attr))

        finally:
            wm.progress_end()
            sko_set_status_text(context, None)

        summary_parts = []
        if created > 0:
            summary_parts.append(f"created {created}")
        if overwritten > 0:
            summary_parts.append(f"overwrote {overwritten}")
        if skipped > 0:
            summary_parts.append(f"skipped {skipped}")

        if not summary_parts:
            summary = "No shapekeys transferred"
            icon = {'WARNING'}
        else:
            summary = f"Transfer complete: {', '.join(summary_parts)}"
            icon = {'INFO'}

        self.report(icon, summary)
        return {'FINISHED'}


class SKO_OT_GroupAdd(Operator):
    bl_idname = "shapekey_organizer.group_add"
    bl_label = "Add"
    bl_description = (
        "Add the typed group name to the Groups list (no duplicates) and assign it to currently selected shapekeys. "
        "If the group already exists, it becomes the active selection."
    )
    bl_options = {'REGISTER', 'UNDO'}

    group: StringProperty(
        name="Group",
        description="Group name to create/assign",
        default=""
    )

    def execute(self, context):
        scn = context.scene
        props = scn.shapekey_organizer

        name = (self.group or props.group_search or "").strip()
        if not name:
            self.report({'WARNING'}, "Enter a group name to add.")
            return {'CANCELLED'}

        groups = scn.sko_groups
        existed = any(g.name == name for g in groups)

        ensure_group(context, name)
        for i, g in enumerate(groups):
            if g.name == name:
                scn.sko_groups_index = i
                break
        props.group_search = name

        assigned = 0
        obj = active_obj_mesh(context)
        if obj:
            sk = getattr(getattr(obj.data, 'shape_keys', None), 'key_blocks', None)
            all_keys = list(sk) if sk else []
    
            selected = [k for k in all_keys if get_sel(k) and not is_basis_key(obj, k)]
            if selected:
                targets = selected
            else:
                idx = getattr(obj, "active_shape_key_index", -1)
                ak = sk[idx] if (sk and 0 <= idx < len(sk)) else None
                targets = [ak] if (ak and not is_basis_key(obj, ak)) else []
    
            for k in targets:
                set_group(k, name)
                assigned += 1

        try:
            for area in context.screen.areas:
                if area.type == 'PROPERTIES':
                    area.tag_redraw()
        except Exception:
            pass

        if existed:
            self.report({'INFO'}, f"Selected existing group '{name}'. Assigned to {assigned} keys.")
        else:
            self.report({'INFO'}, f"Added group '{name}'. Assigned to {assigned} keys.")
        return {'FINISHED'}


class SKO_OT_GroupRemove(Operator):
    bl_idname = "shapekey_organizer.group_remove"
    bl_label = "Remove"
    bl_description = "Remove the selected group from the list and clear it from all assigned shapekeys"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        scn = context.scene
        idx = scn.sko_groups_index
        groups = scn.sko_groups
        if idx < 0 or idx >= len(groups):
            return {'CANCELLED'}

        group_name = groups[idx].name

        obj = active_obj_mesh(context)
        removed_count = 0
        if obj:
            for k in iter_keyblocks(obj):
                if get_group(k) == group_name:
                    set_group(k, "")
                    removed_count += 1

        groups.remove(idx)
        scn.sko_groups_index = min(idx, len(groups) - 1)

        self.report({'INFO'}, f"Removed group '{group_name}' from list and cleared from {removed_count} keys.")
        for area in context.screen.areas:
            if area.type == 'PROPERTIES':
                area.tag_redraw()
        return {'FINISHED'}


class SKO_OT_GroupMove(Operator):
    bl_idname = "shapekey_organizer.group_move"
    bl_label = "Move"
    bl_description = "Reorder groups in the list"
    bl_options = {'REGISTER', 'UNDO'}

    direction: EnumProperty(items=[('UP','Up',''),('DOWN','Down','')], default='UP')

    def execute(self, context):
        scn = context.scene
        idx = scn.sko_groups_index
        groups = scn.sko_groups
        if idx < 0 or idx >= len(groups):
            return {'CANCELLED'}
        new_idx = idx - 1 if self.direction == 'UP' else idx + 1
        if new_idx < 0 or new_idx >= len(groups):
            return {'CANCELLED'}
        groups.move(idx, new_idx)
        scn.sko_groups_index = new_idx
        return {'FINISHED'}


class SKO_OT_GroupSelectKeys(Operator):
    bl_idname = "shapekey_organizer.group_select_keys"
    bl_label = "Select Keys"
    bl_description = "Select all keys tagged with the selected group (ignores Basis)"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        obj = context.object
        if not obj or obj.type != 'MESH':
            return {'CANCELLED'}
        scn = context.scene
        idx = scn.sko_groups_index
        groups = scn.sko_groups
        if idx < 0 or idx >= len(groups):
            return {'CANCELLED'}
        gname = groups[idx].name
        for k in iter_keyblocks(obj):
            if is_basis_key(obj, k):
                continue
            if get_group(k) == gname:
                set_sel(k, True)
        return {'FINISHED'}


class SKO_OT_GroupFilterApply(Operator):
    bl_idname = "shapekey_organizer.group_filter_apply"
    bl_label = "Filter"
    bl_description = "Filter the shapekey list to the selected group"
    bl_options = {'REGISTER'}

    def execute(self, context):
        scn = context.scene
        props = scn.shapekey_organizer
        idx = scn.sko_groups_index
        if idx < 0 or idx >= len(scn.sko_groups):
            return {'CANCELLED'}
        props.filter_group = scn.sko_groups[idx].name
        return {'FINISHED'}


class SKO_OT_GroupFilterClear(Operator):
    bl_idname = "shapekey_organizer.group_filter_clear"
    bl_label = "Clear Filter"
    bl_description = "Clear the group filter in the list"
    bl_options = {'REGISTER'}

    def execute(self, context):
        props = context.scene.shapekey_organizer
        props.filter_group = ""
        return {'FINISHED'}

# =====================================================
# Panel
# =====================================================

class SKO_PT_Main(Panel):
    bl_label = "Blender Shapekey Add-Ons"
    bl_idname = "SKO_PT_main"
    bl_space_type = 'PROPERTIES'
    bl_region_type = 'WINDOW'
    bl_context = "data"

    @classmethod
    def poll(cls, context):
        obj = active_obj_mesh(context)
        return obj and getattr(getattr(obj.data, 'shape_keys', None), 'key_blocks', None)

    def draw(self, context):
        layout = self.layout
        obj = context.object
        props = context.scene.shapekey_organizer

        # Updates
        entry = bpy.context.preferences.addons.get(_ADDON_ID)
        prefs = entry.preferences if entry else None
        row = layout.row(align=True)
        if prefs:
            row.prop(prefs, "auto_check", text="Check on Startup")
        row.operator("shapekey_organizer.check_updates", text="Check for Updates", icon='FILE_REFRESH')
        row = layout.row(align=True)
        row.alignment = 'RIGHT'
        row.label(text=f"Installed: v{current_version_display()}")

        # Filters
        state_edit = bool(getattr(obj, "use_shape_key_edit_mode", False))
        state_solo = bool(getattr(obj, "show_only_shape_key", False))

        box = layout.box()
        row = box.row(align=True)
        row.prop(props, 'search', text="Search")
        layout.separator()
        row.operator("shapekey_organizer.toggle_show_only",
            text="", icon=('SOLO_ON' if obj.show_only_shape_key else 'SOLO_OFF'), depress=state_solo)
        row.operator("shapekey_organizer.toggle_use_edit_mode",
            text="", icon=('EDITMODE_HLT'), depress=state_edit)

        # List
        list_row = box.row(align=True)
        list_row.template_list("SKO_UL_shapekeys", "", obj.data.shape_keys, "key_blocks", obj, "active_shape_key_index", rows=10)
        if obj.data.shape_keys and obj.active_shape_key_index >= 0:
            active_key = obj.data.shape_keys.key_blocks[obj.active_shape_key_index]
            vg_row = box.row(align=True)
            vg_row.prop_search(active_key, "vertex_group", obj, "vertex_groups", text="Vertex Group", icon='GROUP_VERTEX')
        sub = box.box()
        row = sub.row(align=True)
        row.operator("shapekey_organizer.shape_key_add", text="Create…", icon='ADD')
        row.operator("shapekey_organizer.shape_key_delete", text="Delete", icon='TRASH')
        controls = sub.row(align=True)
        controls.operator("shapekey_organizer.select_all", icon='CHECKBOX_HLT')
        controls.operator("shapekey_organizer.select_none", icon='CHECKBOX_DEHLT')
        controls.operator("shapekey_organizer.select_invert", icon='ARROW_LEFTRIGHT')
        controls.operator("shapekey_organizer.sync_state", icon='FILE_REFRESH')
        sub.label(text="Tip: Shift-click a checkbox to select or unselect a range.")
        sub.label(text="When no keys are selected, operations apply to the active key.")

        # Ordering
        sm = layout.box()
        sm.label(text="Ordering")
        row = sm.row(align=True)
        row.prop(props, 'sort_mode', text="")
        row.operator("shapekey_organizer.sort", icon='SORTALPHA')
        row = sm.row(align=True)
        row.operator("shapekey_organizer.move_selected", text="Top", icon="TRIA_UP_BAR").direction = 'TOP'
        row.operator("shapekey_organizer.move_selected", text="Up", icon="TRIA_UP").direction = 'UP'
        row.operator("shapekey_organizer.move_selected", text="Down", icon="TRIA_DOWN").direction = 'DOWN'
        row.operator("shapekey_organizer.move_selected", text="Bottom", icon="TRIA_DOWN_BAR").direction = 'BOTTOM'

        # Groups
        grp = layout.box()
        hdr = grp.row(align=True)
        icon = 'TRIA_DOWN' if props.show_groups else 'TRIA_RIGHT'
        hdr.prop(props, 'show_groups', text="", icon=icon, emboss=False)
        hdr.label(text="Groups")
        if props.show_groups:
            r = grp.row(align=True)
            r.prop(props, 'group_search', text="Group")
            r.operator("shapekey_organizer.group_add", text="Add", icon='ADD')

            rr = grp.row(align=True)
            rr.template_list("SKO_UL_groups", "", context.scene, "sko_groups", context.scene, "sko_groups_index", rows=5)
            col = rr.column(align=True)
            col.operator("shapekey_organizer.group_move", text="Up", icon="TRIA_UP").direction = 'UP'
            col.operator("shapekey_organizer.group_move", text="Down", icon="TRIA_DOWN").direction = 'DOWN'
            col.separator()
            col.operator("shapekey_organizer.group_remove", text="Remove", icon='REMOVE')

            r2 = grp.row(align=True)
            r2.operator("shapekey_organizer.group_select_keys", text="Select Keys", icon='RESTRICT_SELECT_OFF')
            r2.operator("shapekey_organizer.group_filter_apply", text="Filter", icon='FILTER')
            r2.operator("shapekey_organizer.group_filter_clear", text="Clear Filter", icon='X')
            grp.label(text=f"Active filter: '{props.filter_group or 'None'}'")

        # Rename
        rn = layout.box()
        hdr = rn.row(align=True)
        icon = 'TRIA_DOWN' if props.show_rename else 'TRIA_RIGHT'
        hdr.prop(props, 'show_rename', text="", icon=icon, emboss=False)
        hdr.label(text="Rename")
        if props.show_rename:
            row = rn.row(align=True)
            row.prop(props, 'prefix')
            row.separator()
            row.prop(props, 'suffix')
            rn.operator("shapekey_organizer.add_prefix_suffix")

            rn.separator()

            row = rn.row(align=True)
            row.prop(props, 'find')
            row.separator()
            row.prop(props, 'replace')
            rn.operator("shapekey_organizer.find_replace")
            row = rn.row(align=True)
            row.prop(props, 'find_case_sensitive', text='Case-Sensitive')

            rn.separator()

            row = rn.row(align=True)
            row.prop(props, 'auto_number_start')
            row.prop(props, 'auto_number_pad')
            rn.operator("shapekey_organizer.auto_number")

        # Transfer
        tf = layout.box()
        hdr = tf.row(align=True)

        icon = 'TRIA_DOWN' if props.show_transfer else 'TRIA_RIGHT'
        hdr.prop(props, 'show_transfer', text="", icon=icon, emboss=False)
        hdr.label(text="Transfer Shapekeys (EXPERIMENTAL)")
        if props.show_transfer:
            box = tf.box()
            box.label(text="Warning", icon='ERROR')

            col = box.column()
            col.scale_y = 0.9
            col.label(text="Transfer shapekeys BEFORE modifying the mesh.")
            col.label(text="Transferring onto already-fitted assets may cause distorted deformations.")
            col.label(text="Ensure both meshes are in the same rest pose.")

            row = tf.row()
            row.prop(props, "transfer_target", text="Target")
            row = tf.row()
            row.prop(props, "transfer_mode", text="Mode")

            if props.transfer_mode != 'MATCH_TOPOLOGY':
                row = tf.row()
                row.prop(props, "transfer_distance_ratio", text="Max Dist (ratio)")

            row = tf.row(align=True)
            row.prop(props, "transfer_create_missing")
            row.prop(props, "transfer_overwrite_existing")

            row = tf.row()
            row.prop(props, "transfer_copy_settings")

            src = active_obj_mesh(context)
            src_name = src.name if src else "<none>"
            dst_name = props.transfer_target.name if props.transfer_target else "<none>"

            box = tf.box()
            box.label(text=f"Source: {src_name}")
            box.label(text=f"Target: {dst_name}")

            if src:
                selected_keys = [k for k in filtered_keys(context, src) if get_sel(k)]
                box.label(text=f"Selected keys: {len(selected_keys)}")

            row = tf.row()
            row.operator("shapekey_organizer.transfer_selected", icon='CON_TRANSLIKE')

        # Batch edits
        bt = layout.box()
        hdr = bt.row(align=True)
        icon = 'TRIA_DOWN' if props.show_batch else 'TRIA_RIGHT'
        hdr.prop(props, 'show_batch', text="", icon=icon, emboss=False)
        hdr.label(text="Batch Edits")
        if props.show_batch:
            row = bt.row(align=True)
            row.prop(props, 'slider_min')
            row.prop(props, 'slider_max')
            bt.operator("shapekey_organizer.set_slider_range")
            row = bt.row(align=True)
            row.operator("shapekey_organizer.toggle_mute", text="Mute").state = 'ON'
            row.operator("shapekey_organizer.toggle_mute", text="Unmute").state = 'OFF'
            row.operator("shapekey_organizer.toggle_mute", text="Toggle").state = 'TOGGLE'
            bt.operator("shapekey_organizer.reset_values")
            bt.operator("shapekey_organizer.select_empty", text="Select Empty Keys")

        layout.prop(props, 'affect_only_selected')

# =====================================================
# Registration
# =====================================================

classes = (
    SKO_Item,
    SKO_GroupItem,
    SKO_Props,
    SKO_AddonPreferences,
    SKO_UL_ShapeKeys,
    SKO_UL_Groups,
    SKO_OT_TransferSelectedShapeKeys,
    SKO_OT_SelectEmptyShapeKeys,
    SKO_OT_ToggleUseEditMode,
    SKO_OT_ToggleShowOnly,
    SKO_OT_KeyActivateOrRename,
    SKO_OT_ShapeKeyAdd,
    SKO_OT_ShapeKeyDelete,
    SKO_OT_CheckUpdates,
    SKO_OT_ToggleSelect,
    SKO_OT_SelectAll,
    SKO_OT_SelectNone,
    SKO_OT_SelectInvert,
    SKO_OT_AssignGroup,
    SKO_OT_ClearGroup,
    SKO_OT_PrefixSuffix,
    SKO_OT_FindReplace,
    SKO_OT_AutoNumber,
    SKO_OT_Sort,
    SKO_OT_MoveSelected,
    SKO_OT_ToggleMute,
    SKO_OT_SetSliderRange,
    SKO_OT_ResetValues,
    SKO_OT_SyncState,
    SKO_OT_GroupAdd,
    SKO_OT_GroupRemove,
    SKO_OT_GroupMove,
    SKO_OT_GroupSelectKeys,
    SKO_OT_GroupFilterApply,
    SKO_OT_GroupFilterClear,
    SKO_PT_Main,
)


def register():
    for c in classes:
        bpy.utils.register_class(c)
    bpy.types.Scene.shapekey_organizer = bpy.props.PointerProperty(type=SKO_Props)
    bpy.types.Scene.sko_items = CollectionProperty(type=SKO_Item)
    bpy.types.Scene.sko_groups = CollectionProperty(type=SKO_GroupItem)
    bpy.types.Scene.sko_groups_index = IntProperty(default=-1)

    if _sko_auto_check not in bpy.app.handlers.load_post:
        bpy.app.handlers.load_post.append(_sko_auto_check)


def unregister():
    try:
        if _sko_auto_check in bpy.app.handlers.load_post:
            bpy.app.handlers.load_post.remove(_sko_auto_check)
    except Exception:
        pass

    for c in reversed(classes):
        bpy.utils.unregister_class(c)
    del bpy.types.Scene.shapekey_organizer
    if hasattr(bpy.types.Scene, 'sko_items'):
        del bpy.types.Scene.sko_items
    if hasattr(bpy.types.Scene, 'sko_groups'):
        del bpy.types.Scene.sko_groups
    if hasattr(bpy.types.Scene, 'sko_groups_index'):
        del bpy.types.Scene.sko_groups_index


if __name__ == "__main__":
    register()