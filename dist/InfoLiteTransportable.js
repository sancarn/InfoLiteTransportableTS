var __defProp = Object.defineProperty;
var __defNormalProp = (obj, key, value) => key in obj ? __defProp(obj, key, { enumerable: true, configurable: true, writable: true, value }) : obj[key] = value;
var __publicField = (obj, key, value) => __defNormalProp(obj, typeof key !== "symbol" ? key + "" : key, value);

// node_modules/@zip.js/zip.js/lib/core/streams/codecs/deflate.js
var MAX_BITS = 15;
var D_CODES = 30;
var BL_CODES = 19;
var LENGTH_CODES = 29;
var LITERALS = 256;
var L_CODES = LITERALS + 1 + LENGTH_CODES;
var HEAP_SIZE = 2 * L_CODES + 1;
var END_BLOCK = 256;
var MAX_BL_BITS = 7;
var REP_3_6 = 16;
var REPZ_3_10 = 17;
var REPZ_11_138 = 18;
var Buf_size = 8 * 2;
var Z_DEFAULT_COMPRESSION = -1;
var Z_FILTERED = 1;
var Z_HUFFMAN_ONLY = 2;
var Z_DEFAULT_STRATEGY = 0;
var Z_NO_FLUSH = 0;
var Z_PARTIAL_FLUSH = 1;
var Z_FULL_FLUSH = 3;
var Z_FINISH = 4;
var Z_OK = 0;
var Z_STREAM_END = 1;
var Z_NEED_DICT = 2;
var Z_STREAM_ERROR = -2;
var Z_DATA_ERROR = -3;
var Z_BUF_ERROR = -5;
function extractArray(array) {
  return flatArray(array.map(([length, value]) => new Array(length).fill(value, 0, length)));
}
function flatArray(array) {
  return array.reduce((a, b) => a.concat(Array.isArray(b) ? flatArray(b) : b), []);
}
var _dist_code = [0, 1, 2, 3].concat(...extractArray([
  [2, 4],
  [2, 5],
  [4, 6],
  [4, 7],
  [8, 8],
  [8, 9],
  [16, 10],
  [16, 11],
  [32, 12],
  [32, 13],
  [64, 14],
  [64, 15],
  [2, 0],
  [1, 16],
  [1, 17],
  [2, 18],
  [2, 19],
  [4, 20],
  [4, 21],
  [8, 22],
  [8, 23],
  [16, 24],
  [16, 25],
  [32, 26],
  [32, 27],
  [64, 28],
  [64, 29]
]));
function Tree() {
  const that = this;
  function gen_bitlen(s) {
    const tree = that.dyn_tree;
    const stree = that.stat_desc.static_tree;
    const extra = that.stat_desc.extra_bits;
    const base = that.stat_desc.extra_base;
    const max_length = that.stat_desc.max_length;
    let h;
    let n, m;
    let bits;
    let xbits;
    let f;
    let overflow = 0;
    for (bits = 0; bits <= MAX_BITS; bits++)
      s.bl_count[bits] = 0;
    tree[s.heap[s.heap_max] * 2 + 1] = 0;
    for (h = s.heap_max + 1; h < HEAP_SIZE; h++) {
      n = s.heap[h];
      bits = tree[tree[n * 2 + 1] * 2 + 1] + 1;
      if (bits > max_length) {
        bits = max_length;
        overflow++;
      }
      tree[n * 2 + 1] = bits;
      if (n > that.max_code)
        continue;
      s.bl_count[bits]++;
      xbits = 0;
      if (n >= base)
        xbits = extra[n - base];
      f = tree[n * 2];
      s.opt_len += f * (bits + xbits);
      if (stree)
        s.static_len += f * (stree[n * 2 + 1] + xbits);
    }
    if (overflow === 0)
      return;
    do {
      bits = max_length - 1;
      while (s.bl_count[bits] === 0)
        bits--;
      s.bl_count[bits]--;
      s.bl_count[bits + 1] += 2;
      s.bl_count[max_length]--;
      overflow -= 2;
    } while (overflow > 0);
    for (bits = max_length; bits !== 0; bits--) {
      n = s.bl_count[bits];
      while (n !== 0) {
        m = s.heap[--h];
        if (m > that.max_code)
          continue;
        if (tree[m * 2 + 1] != bits) {
          s.opt_len += (bits - tree[m * 2 + 1]) * tree[m * 2];
          tree[m * 2 + 1] = bits;
        }
        n--;
      }
    }
  }
  function bi_reverse(code, len) {
    let res = 0;
    do {
      res |= code & 1;
      code >>>= 1;
      res <<= 1;
    } while (--len > 0);
    return res >>> 1;
  }
  function gen_codes(tree, max_code, bl_count) {
    const next_code = [];
    let code = 0;
    let bits;
    let n;
    let len;
    for (bits = 1; bits <= MAX_BITS; bits++) {
      next_code[bits] = code = code + bl_count[bits - 1] << 1;
    }
    for (n = 0; n <= max_code; n++) {
      len = tree[n * 2 + 1];
      if (len === 0)
        continue;
      tree[n * 2] = bi_reverse(next_code[len]++, len);
    }
  }
  that.build_tree = function(s) {
    const tree = that.dyn_tree;
    const stree = that.stat_desc.static_tree;
    const elems = that.stat_desc.elems;
    let n, m;
    let max_code = -1;
    let node;
    s.heap_len = 0;
    s.heap_max = HEAP_SIZE;
    for (n = 0; n < elems; n++) {
      if (tree[n * 2] !== 0) {
        s.heap[++s.heap_len] = max_code = n;
        s.depth[n] = 0;
      } else {
        tree[n * 2 + 1] = 0;
      }
    }
    while (s.heap_len < 2) {
      node = s.heap[++s.heap_len] = max_code < 2 ? ++max_code : 0;
      tree[node * 2] = 1;
      s.depth[node] = 0;
      s.opt_len--;
      if (stree)
        s.static_len -= stree[node * 2 + 1];
    }
    that.max_code = max_code;
    for (n = Math.floor(s.heap_len / 2); n >= 1; n--)
      s.pqdownheap(tree, n);
    node = elems;
    do {
      n = s.heap[1];
      s.heap[1] = s.heap[s.heap_len--];
      s.pqdownheap(tree, 1);
      m = s.heap[1];
      s.heap[--s.heap_max] = n;
      s.heap[--s.heap_max] = m;
      tree[node * 2] = tree[n * 2] + tree[m * 2];
      s.depth[node] = Math.max(s.depth[n], s.depth[m]) + 1;
      tree[n * 2 + 1] = tree[m * 2 + 1] = node;
      s.heap[1] = node++;
      s.pqdownheap(tree, 1);
    } while (s.heap_len >= 2);
    s.heap[--s.heap_max] = s.heap[1];
    gen_bitlen(s);
    gen_codes(tree, that.max_code, s.bl_count);
  };
}
Tree._length_code = [0, 1, 2, 3, 4, 5, 6, 7].concat(...extractArray([
  [2, 8],
  [2, 9],
  [2, 10],
  [2, 11],
  [4, 12],
  [4, 13],
  [4, 14],
  [4, 15],
  [8, 16],
  [8, 17],
  [8, 18],
  [8, 19],
  [16, 20],
  [16, 21],
  [16, 22],
  [16, 23],
  [32, 24],
  [32, 25],
  [32, 26],
  [31, 27],
  [1, 28]
]));
Tree.base_length = [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 20, 24, 28, 32, 40, 48, 56, 64, 80, 96, 112, 128, 160, 192, 224, 0];
Tree.base_dist = [
  0,
  1,
  2,
  3,
  4,
  6,
  8,
  12,
  16,
  24,
  32,
  48,
  64,
  96,
  128,
  192,
  256,
  384,
  512,
  768,
  1024,
  1536,
  2048,
  3072,
  4096,
  6144,
  8192,
  12288,
  16384,
  24576
];
Tree.d_code = function(dist) {
  return dist < 256 ? _dist_code[dist] : _dist_code[256 + (dist >>> 7)];
};
Tree.extra_lbits = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
Tree.extra_dbits = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
Tree.extra_blbits = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 7];
Tree.bl_order = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
function StaticTree(static_tree, extra_bits, extra_base, elems, max_length) {
  const that = this;
  that.static_tree = static_tree;
  that.extra_bits = extra_bits;
  that.extra_base = extra_base;
  that.elems = elems;
  that.max_length = max_length;
}
var static_ltree2_first_part = [
  12,
  140,
  76,
  204,
  44,
  172,
  108,
  236,
  28,
  156,
  92,
  220,
  60,
  188,
  124,
  252,
  2,
  130,
  66,
  194,
  34,
  162,
  98,
  226,
  18,
  146,
  82,
  210,
  50,
  178,
  114,
  242,
  10,
  138,
  74,
  202,
  42,
  170,
  106,
  234,
  26,
  154,
  90,
  218,
  58,
  186,
  122,
  250,
  6,
  134,
  70,
  198,
  38,
  166,
  102,
  230,
  22,
  150,
  86,
  214,
  54,
  182,
  118,
  246,
  14,
  142,
  78,
  206,
  46,
  174,
  110,
  238,
  30,
  158,
  94,
  222,
  62,
  190,
  126,
  254,
  1,
  129,
  65,
  193,
  33,
  161,
  97,
  225,
  17,
  145,
  81,
  209,
  49,
  177,
  113,
  241,
  9,
  137,
  73,
  201,
  41,
  169,
  105,
  233,
  25,
  153,
  89,
  217,
  57,
  185,
  121,
  249,
  5,
  133,
  69,
  197,
  37,
  165,
  101,
  229,
  21,
  149,
  85,
  213,
  53,
  181,
  117,
  245,
  13,
  141,
  77,
  205,
  45,
  173,
  109,
  237,
  29,
  157,
  93,
  221,
  61,
  189,
  125,
  253,
  19,
  275,
  147,
  403,
  83,
  339,
  211,
  467,
  51,
  307,
  179,
  435,
  115,
  371,
  243,
  499,
  11,
  267,
  139,
  395,
  75,
  331,
  203,
  459,
  43,
  299,
  171,
  427,
  107,
  363,
  235,
  491,
  27,
  283,
  155,
  411,
  91,
  347,
  219,
  475,
  59,
  315,
  187,
  443,
  123,
  379,
  251,
  507,
  7,
  263,
  135,
  391,
  71,
  327,
  199,
  455,
  39,
  295,
  167,
  423,
  103,
  359,
  231,
  487,
  23,
  279,
  151,
  407,
  87,
  343,
  215,
  471,
  55,
  311,
  183,
  439,
  119,
  375,
  247,
  503,
  15,
  271,
  143,
  399,
  79,
  335,
  207,
  463,
  47,
  303,
  175,
  431,
  111,
  367,
  239,
  495,
  31,
  287,
  159,
  415,
  95,
  351,
  223,
  479,
  63,
  319,
  191,
  447,
  127,
  383,
  255,
  511,
  0,
  64,
  32,
  96,
  16,
  80,
  48,
  112,
  8,
  72,
  40,
  104,
  24,
  88,
  56,
  120,
  4,
  68,
  36,
  100,
  20,
  84,
  52,
  116,
  3,
  131,
  67,
  195,
  35,
  163,
  99,
  227
];
var static_ltree2_second_part = extractArray([[144, 8], [112, 9], [24, 7], [8, 8]]);
StaticTree.static_ltree = flatArray(static_ltree2_first_part.map((value, index) => [value, static_ltree2_second_part[index]]));
var static_dtree_first_part = [0, 16, 8, 24, 4, 20, 12, 28, 2, 18, 10, 26, 6, 22, 14, 30, 1, 17, 9, 25, 5, 21, 13, 29, 3, 19, 11, 27, 7, 23];
var static_dtree_second_part = extractArray([[30, 5]]);
StaticTree.static_dtree = flatArray(static_dtree_first_part.map((value, index) => [value, static_dtree_second_part[index]]));
StaticTree.static_l_desc = new StaticTree(StaticTree.static_ltree, Tree.extra_lbits, LITERALS + 1, L_CODES, MAX_BITS);
StaticTree.static_d_desc = new StaticTree(StaticTree.static_dtree, Tree.extra_dbits, 0, D_CODES, MAX_BITS);
StaticTree.static_bl_desc = new StaticTree(null, Tree.extra_blbits, 0, BL_CODES, MAX_BL_BITS);
var MAX_MEM_LEVEL = 9;
var DEF_MEM_LEVEL = 8;
function Config(good_length, max_lazy, nice_length, max_chain, func) {
  const that = this;
  that.good_length = good_length;
  that.max_lazy = max_lazy;
  that.nice_length = nice_length;
  that.max_chain = max_chain;
  that.func = func;
}
var STORED = 0;
var FAST = 1;
var SLOW = 2;
var config_table = [
  new Config(0, 0, 0, 0, STORED),
  new Config(4, 4, 8, 4, FAST),
  new Config(4, 5, 16, 8, FAST),
  new Config(4, 6, 32, 32, FAST),
  new Config(4, 4, 16, 16, SLOW),
  new Config(8, 16, 32, 32, SLOW),
  new Config(8, 16, 128, 128, SLOW),
  new Config(8, 32, 128, 256, SLOW),
  new Config(32, 128, 258, 1024, SLOW),
  new Config(32, 258, 258, 4096, SLOW)
];
var z_errmsg = [
  "need dictionary",
  // Z_NEED_DICT
  // 2
  "stream end",
  // Z_STREAM_END 1
  "",
  // Z_OK 0
  "",
  // Z_ERRNO (-1)
  "stream error",
  // Z_STREAM_ERROR (-2)
  "data error",
  // Z_DATA_ERROR (-3)
  "",
  // Z_MEM_ERROR (-4)
  "buffer error",
  // Z_BUF_ERROR (-5)
  "",
  // Z_VERSION_ERROR (-6)
  ""
];
var NeedMore = 0;
var BlockDone = 1;
var FinishStarted = 2;
var FinishDone = 3;
var PRESET_DICT = 32;
var INIT_STATE = 42;
var BUSY_STATE = 113;
var FINISH_STATE = 666;
var Z_DEFLATED = 8;
var STORED_BLOCK = 0;
var STATIC_TREES = 1;
var DYN_TREES = 2;
var MIN_MATCH = 3;
var MAX_MATCH = 258;
var MIN_LOOKAHEAD = MAX_MATCH + MIN_MATCH + 1;
function smaller(tree, n, m, depth) {
  const tn2 = tree[n * 2];
  const tm2 = tree[m * 2];
  return tn2 < tm2 || tn2 == tm2 && depth[n] <= depth[m];
}
function Deflate() {
  const that = this;
  let strm;
  let status;
  let pending_buf_size;
  let last_flush;
  let w_size;
  let w_bits;
  let w_mask;
  let win;
  let window_size;
  let prev;
  let head;
  let ins_h;
  let hash_size;
  let hash_bits;
  let hash_mask;
  let hash_shift;
  let block_start;
  let match_length;
  let prev_match;
  let match_available;
  let strstart;
  let match_start;
  let lookahead;
  let prev_length;
  let max_chain_length;
  let max_lazy_match;
  let level;
  let strategy;
  let good_match;
  let nice_match;
  let dyn_ltree;
  let dyn_dtree;
  let bl_tree;
  const l_desc = new Tree();
  const d_desc = new Tree();
  const bl_desc = new Tree();
  that.depth = [];
  let lit_bufsize;
  let last_lit;
  let matches;
  let last_eob_len;
  let bi_buf;
  let bi_valid;
  that.bl_count = [];
  that.heap = [];
  dyn_ltree = [];
  dyn_dtree = [];
  bl_tree = [];
  function lm_init() {
    window_size = 2 * w_size;
    head[hash_size - 1] = 0;
    for (let i = 0; i < hash_size - 1; i++) {
      head[i] = 0;
    }
    max_lazy_match = config_table[level].max_lazy;
    good_match = config_table[level].good_length;
    nice_match = config_table[level].nice_length;
    max_chain_length = config_table[level].max_chain;
    strstart = 0;
    block_start = 0;
    lookahead = 0;
    match_length = prev_length = MIN_MATCH - 1;
    match_available = 0;
    ins_h = 0;
  }
  function init_block() {
    let i;
    for (i = 0; i < L_CODES; i++)
      dyn_ltree[i * 2] = 0;
    for (i = 0; i < D_CODES; i++)
      dyn_dtree[i * 2] = 0;
    for (i = 0; i < BL_CODES; i++)
      bl_tree[i * 2] = 0;
    dyn_ltree[END_BLOCK * 2] = 1;
    that.opt_len = that.static_len = 0;
    last_lit = matches = 0;
  }
  function tr_init() {
    l_desc.dyn_tree = dyn_ltree;
    l_desc.stat_desc = StaticTree.static_l_desc;
    d_desc.dyn_tree = dyn_dtree;
    d_desc.stat_desc = StaticTree.static_d_desc;
    bl_desc.dyn_tree = bl_tree;
    bl_desc.stat_desc = StaticTree.static_bl_desc;
    bi_buf = 0;
    bi_valid = 0;
    last_eob_len = 8;
    init_block();
  }
  that.pqdownheap = function(tree, k) {
    const heap = that.heap;
    const v = heap[k];
    let j = k << 1;
    while (j <= that.heap_len) {
      if (j < that.heap_len && smaller(tree, heap[j + 1], heap[j], that.depth)) {
        j++;
      }
      if (smaller(tree, v, heap[j], that.depth))
        break;
      heap[k] = heap[j];
      k = j;
      j <<= 1;
    }
    heap[k] = v;
  };
  function scan_tree(tree, max_code) {
    let prevlen = -1;
    let curlen;
    let nextlen = tree[0 * 2 + 1];
    let count = 0;
    let max_count = 7;
    let min_count = 4;
    if (nextlen === 0) {
      max_count = 138;
      min_count = 3;
    }
    tree[(max_code + 1) * 2 + 1] = 65535;
    for (let n = 0; n <= max_code; n++) {
      curlen = nextlen;
      nextlen = tree[(n + 1) * 2 + 1];
      if (++count < max_count && curlen == nextlen) {
        continue;
      } else if (count < min_count) {
        bl_tree[curlen * 2] += count;
      } else if (curlen !== 0) {
        if (curlen != prevlen)
          bl_tree[curlen * 2]++;
        bl_tree[REP_3_6 * 2]++;
      } else if (count <= 10) {
        bl_tree[REPZ_3_10 * 2]++;
      } else {
        bl_tree[REPZ_11_138 * 2]++;
      }
      count = 0;
      prevlen = curlen;
      if (nextlen === 0) {
        max_count = 138;
        min_count = 3;
      } else if (curlen == nextlen) {
        max_count = 6;
        min_count = 3;
      } else {
        max_count = 7;
        min_count = 4;
      }
    }
  }
  function build_bl_tree() {
    let max_blindex;
    scan_tree(dyn_ltree, l_desc.max_code);
    scan_tree(dyn_dtree, d_desc.max_code);
    bl_desc.build_tree(that);
    for (max_blindex = BL_CODES - 1; max_blindex >= 3; max_blindex--) {
      if (bl_tree[Tree.bl_order[max_blindex] * 2 + 1] !== 0)
        break;
    }
    that.opt_len += 3 * (max_blindex + 1) + 5 + 5 + 4;
    return max_blindex;
  }
  function put_byte(p) {
    that.pending_buf[that.pending++] = p;
  }
  function put_short(w) {
    put_byte(w & 255);
    put_byte(w >>> 8 & 255);
  }
  function putShortMSB(b) {
    put_byte(b >> 8 & 255);
    put_byte(b & 255 & 255);
  }
  function send_bits(value, length) {
    let val;
    const len = length;
    if (bi_valid > Buf_size - len) {
      val = value;
      bi_buf |= val << bi_valid & 65535;
      put_short(bi_buf);
      bi_buf = val >>> Buf_size - bi_valid;
      bi_valid += len - Buf_size;
    } else {
      bi_buf |= value << bi_valid & 65535;
      bi_valid += len;
    }
  }
  function send_code(c, tree) {
    const c2 = c * 2;
    send_bits(tree[c2] & 65535, tree[c2 + 1] & 65535);
  }
  function send_tree(tree, max_code) {
    let n;
    let prevlen = -1;
    let curlen;
    let nextlen = tree[0 * 2 + 1];
    let count = 0;
    let max_count = 7;
    let min_count = 4;
    if (nextlen === 0) {
      max_count = 138;
      min_count = 3;
    }
    for (n = 0; n <= max_code; n++) {
      curlen = nextlen;
      nextlen = tree[(n + 1) * 2 + 1];
      if (++count < max_count && curlen == nextlen) {
        continue;
      } else if (count < min_count) {
        do {
          send_code(curlen, bl_tree);
        } while (--count !== 0);
      } else if (curlen !== 0) {
        if (curlen != prevlen) {
          send_code(curlen, bl_tree);
          count--;
        }
        send_code(REP_3_6, bl_tree);
        send_bits(count - 3, 2);
      } else if (count <= 10) {
        send_code(REPZ_3_10, bl_tree);
        send_bits(count - 3, 3);
      } else {
        send_code(REPZ_11_138, bl_tree);
        send_bits(count - 11, 7);
      }
      count = 0;
      prevlen = curlen;
      if (nextlen === 0) {
        max_count = 138;
        min_count = 3;
      } else if (curlen == nextlen) {
        max_count = 6;
        min_count = 3;
      } else {
        max_count = 7;
        min_count = 4;
      }
    }
  }
  function send_all_trees(lcodes, dcodes, blcodes) {
    let rank;
    send_bits(lcodes - 257, 5);
    send_bits(dcodes - 1, 5);
    send_bits(blcodes - 4, 4);
    for (rank = 0; rank < blcodes; rank++) {
      send_bits(bl_tree[Tree.bl_order[rank] * 2 + 1], 3);
    }
    send_tree(dyn_ltree, lcodes - 1);
    send_tree(dyn_dtree, dcodes - 1);
  }
  function bi_flush() {
    if (bi_valid == 16) {
      put_short(bi_buf);
      bi_buf = 0;
      bi_valid = 0;
    } else if (bi_valid >= 8) {
      put_byte(bi_buf & 255);
      bi_buf >>>= 8;
      bi_valid -= 8;
    }
  }
  function _tr_align() {
    send_bits(STATIC_TREES << 1, 3);
    send_code(END_BLOCK, StaticTree.static_ltree);
    bi_flush();
    if (1 + last_eob_len + 10 - bi_valid < 9) {
      send_bits(STATIC_TREES << 1, 3);
      send_code(END_BLOCK, StaticTree.static_ltree);
      bi_flush();
    }
    last_eob_len = 7;
  }
  function _tr_tally(dist, lc) {
    let out_length, in_length, dcode;
    that.dist_buf[last_lit] = dist;
    that.lc_buf[last_lit] = lc & 255;
    last_lit++;
    if (dist === 0) {
      dyn_ltree[lc * 2]++;
    } else {
      matches++;
      dist--;
      dyn_ltree[(Tree._length_code[lc] + LITERALS + 1) * 2]++;
      dyn_dtree[Tree.d_code(dist) * 2]++;
    }
    if ((last_lit & 8191) === 0 && level > 2) {
      out_length = last_lit * 8;
      in_length = strstart - block_start;
      for (dcode = 0; dcode < D_CODES; dcode++) {
        out_length += dyn_dtree[dcode * 2] * (5 + Tree.extra_dbits[dcode]);
      }
      out_length >>>= 3;
      if (matches < Math.floor(last_lit / 2) && out_length < Math.floor(in_length / 2))
        return true;
    }
    return last_lit == lit_bufsize - 1;
  }
  function compress_block(ltree, dtree) {
    let dist;
    let lc;
    let lx = 0;
    let code;
    let extra;
    if (last_lit !== 0) {
      do {
        dist = that.dist_buf[lx];
        lc = that.lc_buf[lx];
        lx++;
        if (dist === 0) {
          send_code(lc, ltree);
        } else {
          code = Tree._length_code[lc];
          send_code(code + LITERALS + 1, ltree);
          extra = Tree.extra_lbits[code];
          if (extra !== 0) {
            lc -= Tree.base_length[code];
            send_bits(lc, extra);
          }
          dist--;
          code = Tree.d_code(dist);
          send_code(code, dtree);
          extra = Tree.extra_dbits[code];
          if (extra !== 0) {
            dist -= Tree.base_dist[code];
            send_bits(dist, extra);
          }
        }
      } while (lx < last_lit);
    }
    send_code(END_BLOCK, ltree);
    last_eob_len = ltree[END_BLOCK * 2 + 1];
  }
  function bi_windup() {
    if (bi_valid > 8) {
      put_short(bi_buf);
    } else if (bi_valid > 0) {
      put_byte(bi_buf & 255);
    }
    bi_buf = 0;
    bi_valid = 0;
  }
  function copy_block(buf, len, header) {
    bi_windup();
    last_eob_len = 8;
    if (header) {
      put_short(len);
      put_short(~len);
    }
    that.pending_buf.set(win.subarray(buf, buf + len), that.pending);
    that.pending += len;
  }
  function _tr_stored_block(buf, stored_len, eof) {
    send_bits((STORED_BLOCK << 1) + (eof ? 1 : 0), 3);
    copy_block(buf, stored_len, true);
  }
  function _tr_flush_block(buf, stored_len, eof) {
    let opt_lenb, static_lenb;
    let max_blindex = 0;
    if (level > 0) {
      l_desc.build_tree(that);
      d_desc.build_tree(that);
      max_blindex = build_bl_tree();
      opt_lenb = that.opt_len + 3 + 7 >>> 3;
      static_lenb = that.static_len + 3 + 7 >>> 3;
      if (static_lenb <= opt_lenb)
        opt_lenb = static_lenb;
    } else {
      opt_lenb = static_lenb = stored_len + 5;
    }
    if (stored_len + 4 <= opt_lenb && buf != -1) {
      _tr_stored_block(buf, stored_len, eof);
    } else if (static_lenb == opt_lenb) {
      send_bits((STATIC_TREES << 1) + (eof ? 1 : 0), 3);
      compress_block(StaticTree.static_ltree, StaticTree.static_dtree);
    } else {
      send_bits((DYN_TREES << 1) + (eof ? 1 : 0), 3);
      send_all_trees(l_desc.max_code + 1, d_desc.max_code + 1, max_blindex + 1);
      compress_block(dyn_ltree, dyn_dtree);
    }
    init_block();
    if (eof) {
      bi_windup();
    }
  }
  function flush_block_only(eof) {
    _tr_flush_block(block_start >= 0 ? block_start : -1, strstart - block_start, eof);
    block_start = strstart;
    strm.flush_pending();
  }
  function fill_window() {
    let n, m;
    let p;
    let more;
    do {
      more = window_size - lookahead - strstart;
      if (more === 0 && strstart === 0 && lookahead === 0) {
        more = w_size;
      } else if (more == -1) {
        more--;
      } else if (strstart >= w_size + w_size - MIN_LOOKAHEAD) {
        win.set(win.subarray(w_size, w_size + w_size), 0);
        match_start -= w_size;
        strstart -= w_size;
        block_start -= w_size;
        n = hash_size;
        p = n;
        do {
          m = head[--p] & 65535;
          head[p] = m >= w_size ? m - w_size : 0;
        } while (--n !== 0);
        n = w_size;
        p = n;
        do {
          m = prev[--p] & 65535;
          prev[p] = m >= w_size ? m - w_size : 0;
        } while (--n !== 0);
        more += w_size;
      }
      if (strm.avail_in === 0)
        return;
      n = strm.read_buf(win, strstart + lookahead, more);
      lookahead += n;
      if (lookahead >= MIN_MATCH) {
        ins_h = win[strstart] & 255;
        ins_h = (ins_h << hash_shift ^ win[strstart + 1] & 255) & hash_mask;
      }
    } while (lookahead < MIN_LOOKAHEAD && strm.avail_in !== 0);
  }
  function deflate_stored(flush) {
    let max_block_size = 65535;
    let max_start;
    if (max_block_size > pending_buf_size - 5) {
      max_block_size = pending_buf_size - 5;
    }
    while (true) {
      if (lookahead <= 1) {
        fill_window();
        if (lookahead === 0 && flush == Z_NO_FLUSH)
          return NeedMore;
        if (lookahead === 0)
          break;
      }
      strstart += lookahead;
      lookahead = 0;
      max_start = block_start + max_block_size;
      if (strstart === 0 || strstart >= max_start) {
        lookahead = strstart - max_start;
        strstart = max_start;
        flush_block_only(false);
        if (strm.avail_out === 0)
          return NeedMore;
      }
      if (strstart - block_start >= w_size - MIN_LOOKAHEAD) {
        flush_block_only(false);
        if (strm.avail_out === 0)
          return NeedMore;
      }
    }
    flush_block_only(flush == Z_FINISH);
    if (strm.avail_out === 0)
      return flush == Z_FINISH ? FinishStarted : NeedMore;
    return flush == Z_FINISH ? FinishDone : BlockDone;
  }
  function longest_match(cur_match) {
    let chain_length = max_chain_length;
    let scan = strstart;
    let match;
    let len;
    let best_len = prev_length;
    const limit = strstart > w_size - MIN_LOOKAHEAD ? strstart - (w_size - MIN_LOOKAHEAD) : 0;
    let _nice_match = nice_match;
    const wmask = w_mask;
    const strend = strstart + MAX_MATCH;
    let scan_end1 = win[scan + best_len - 1];
    let scan_end = win[scan + best_len];
    if (prev_length >= good_match) {
      chain_length >>= 2;
    }
    if (_nice_match > lookahead)
      _nice_match = lookahead;
    do {
      match = cur_match;
      if (win[match + best_len] != scan_end || win[match + best_len - 1] != scan_end1 || win[match] != win[scan] || win[++match] != win[scan + 1])
        continue;
      scan += 2;
      match++;
      do {
      } while (win[++scan] == win[++match] && win[++scan] == win[++match] && win[++scan] == win[++match] && win[++scan] == win[++match] && win[++scan] == win[++match] && win[++scan] == win[++match] && win[++scan] == win[++match] && win[++scan] == win[++match] && scan < strend);
      len = MAX_MATCH - (strend - scan);
      scan = strend - MAX_MATCH;
      if (len > best_len) {
        match_start = cur_match;
        best_len = len;
        if (len >= _nice_match)
          break;
        scan_end1 = win[scan + best_len - 1];
        scan_end = win[scan + best_len];
      }
    } while ((cur_match = prev[cur_match & wmask] & 65535) > limit && --chain_length !== 0);
    if (best_len <= lookahead)
      return best_len;
    return lookahead;
  }
  function deflate_fast(flush) {
    let hash_head = 0;
    let bflush;
    while (true) {
      if (lookahead < MIN_LOOKAHEAD) {
        fill_window();
        if (lookahead < MIN_LOOKAHEAD && flush == Z_NO_FLUSH) {
          return NeedMore;
        }
        if (lookahead === 0)
          break;
      }
      if (lookahead >= MIN_MATCH) {
        ins_h = (ins_h << hash_shift ^ win[strstart + (MIN_MATCH - 1)] & 255) & hash_mask;
        hash_head = head[ins_h] & 65535;
        prev[strstart & w_mask] = head[ins_h];
        head[ins_h] = strstart;
      }
      if (hash_head !== 0 && (strstart - hash_head & 65535) <= w_size - MIN_LOOKAHEAD) {
        if (strategy != Z_HUFFMAN_ONLY) {
          match_length = longest_match(hash_head);
        }
      }
      if (match_length >= MIN_MATCH) {
        bflush = _tr_tally(strstart - match_start, match_length - MIN_MATCH);
        lookahead -= match_length;
        if (match_length <= max_lazy_match && lookahead >= MIN_MATCH) {
          match_length--;
          do {
            strstart++;
            ins_h = (ins_h << hash_shift ^ win[strstart + (MIN_MATCH - 1)] & 255) & hash_mask;
            hash_head = head[ins_h] & 65535;
            prev[strstart & w_mask] = head[ins_h];
            head[ins_h] = strstart;
          } while (--match_length !== 0);
          strstart++;
        } else {
          strstart += match_length;
          match_length = 0;
          ins_h = win[strstart] & 255;
          ins_h = (ins_h << hash_shift ^ win[strstart + 1] & 255) & hash_mask;
        }
      } else {
        bflush = _tr_tally(0, win[strstart] & 255);
        lookahead--;
        strstart++;
      }
      if (bflush) {
        flush_block_only(false);
        if (strm.avail_out === 0)
          return NeedMore;
      }
    }
    flush_block_only(flush == Z_FINISH);
    if (strm.avail_out === 0) {
      if (flush == Z_FINISH)
        return FinishStarted;
      else
        return NeedMore;
    }
    return flush == Z_FINISH ? FinishDone : BlockDone;
  }
  function deflate_slow(flush) {
    let hash_head = 0;
    let bflush;
    let max_insert;
    while (true) {
      if (lookahead < MIN_LOOKAHEAD) {
        fill_window();
        if (lookahead < MIN_LOOKAHEAD && flush == Z_NO_FLUSH) {
          return NeedMore;
        }
        if (lookahead === 0)
          break;
      }
      if (lookahead >= MIN_MATCH) {
        ins_h = (ins_h << hash_shift ^ win[strstart + (MIN_MATCH - 1)] & 255) & hash_mask;
        hash_head = head[ins_h] & 65535;
        prev[strstart & w_mask] = head[ins_h];
        head[ins_h] = strstart;
      }
      prev_length = match_length;
      prev_match = match_start;
      match_length = MIN_MATCH - 1;
      if (hash_head !== 0 && prev_length < max_lazy_match && (strstart - hash_head & 65535) <= w_size - MIN_LOOKAHEAD) {
        if (strategy != Z_HUFFMAN_ONLY) {
          match_length = longest_match(hash_head);
        }
        if (match_length <= 5 && (strategy == Z_FILTERED || match_length == MIN_MATCH && strstart - match_start > 4096)) {
          match_length = MIN_MATCH - 1;
        }
      }
      if (prev_length >= MIN_MATCH && match_length <= prev_length) {
        max_insert = strstart + lookahead - MIN_MATCH;
        bflush = _tr_tally(strstart - 1 - prev_match, prev_length - MIN_MATCH);
        lookahead -= prev_length - 1;
        prev_length -= 2;
        do {
          if (++strstart <= max_insert) {
            ins_h = (ins_h << hash_shift ^ win[strstart + (MIN_MATCH - 1)] & 255) & hash_mask;
            hash_head = head[ins_h] & 65535;
            prev[strstart & w_mask] = head[ins_h];
            head[ins_h] = strstart;
          }
        } while (--prev_length !== 0);
        match_available = 0;
        match_length = MIN_MATCH - 1;
        strstart++;
        if (bflush) {
          flush_block_only(false);
          if (strm.avail_out === 0)
            return NeedMore;
        }
      } else if (match_available !== 0) {
        bflush = _tr_tally(0, win[strstart - 1] & 255);
        if (bflush) {
          flush_block_only(false);
        }
        strstart++;
        lookahead--;
        if (strm.avail_out === 0)
          return NeedMore;
      } else {
        match_available = 1;
        strstart++;
        lookahead--;
      }
    }
    if (match_available !== 0) {
      bflush = _tr_tally(0, win[strstart - 1] & 255);
      match_available = 0;
    }
    flush_block_only(flush == Z_FINISH);
    if (strm.avail_out === 0) {
      if (flush == Z_FINISH)
        return FinishStarted;
      else
        return NeedMore;
    }
    return flush == Z_FINISH ? FinishDone : BlockDone;
  }
  function deflateReset(strm2) {
    strm2.total_in = strm2.total_out = 0;
    strm2.msg = null;
    that.pending = 0;
    that.pending_out = 0;
    status = BUSY_STATE;
    last_flush = Z_NO_FLUSH;
    tr_init();
    lm_init();
    return Z_OK;
  }
  that.deflateInit = function(strm2, _level, bits, _method, memLevel, _strategy) {
    if (!_method)
      _method = Z_DEFLATED;
    if (!memLevel)
      memLevel = DEF_MEM_LEVEL;
    if (!_strategy)
      _strategy = Z_DEFAULT_STRATEGY;
    strm2.msg = null;
    if (_level == Z_DEFAULT_COMPRESSION)
      _level = 6;
    if (memLevel < 1 || memLevel > MAX_MEM_LEVEL || _method != Z_DEFLATED || bits < 9 || bits > 15 || _level < 0 || _level > 9 || _strategy < 0 || _strategy > Z_HUFFMAN_ONLY) {
      return Z_STREAM_ERROR;
    }
    strm2.dstate = that;
    w_bits = bits;
    w_size = 1 << w_bits;
    w_mask = w_size - 1;
    hash_bits = memLevel + 7;
    hash_size = 1 << hash_bits;
    hash_mask = hash_size - 1;
    hash_shift = Math.floor((hash_bits + MIN_MATCH - 1) / MIN_MATCH);
    win = new Uint8Array(w_size * 2);
    prev = [];
    head = [];
    lit_bufsize = 1 << memLevel + 6;
    that.pending_buf = new Uint8Array(lit_bufsize * 4);
    pending_buf_size = lit_bufsize * 4;
    that.dist_buf = new Uint16Array(lit_bufsize);
    that.lc_buf = new Uint8Array(lit_bufsize);
    level = _level;
    strategy = _strategy;
    return deflateReset(strm2);
  };
  that.deflateEnd = function() {
    if (status != INIT_STATE && status != BUSY_STATE && status != FINISH_STATE) {
      return Z_STREAM_ERROR;
    }
    that.lc_buf = null;
    that.dist_buf = null;
    that.pending_buf = null;
    head = null;
    prev = null;
    win = null;
    that.dstate = null;
    return status == BUSY_STATE ? Z_DATA_ERROR : Z_OK;
  };
  that.deflateParams = function(strm2, _level, _strategy) {
    let err = Z_OK;
    if (_level == Z_DEFAULT_COMPRESSION) {
      _level = 6;
    }
    if (_level < 0 || _level > 9 || _strategy < 0 || _strategy > Z_HUFFMAN_ONLY) {
      return Z_STREAM_ERROR;
    }
    if (config_table[level].func != config_table[_level].func && strm2.total_in !== 0) {
      err = strm2.deflate(Z_PARTIAL_FLUSH);
    }
    if (level != _level) {
      level = _level;
      max_lazy_match = config_table[level].max_lazy;
      good_match = config_table[level].good_length;
      nice_match = config_table[level].nice_length;
      max_chain_length = config_table[level].max_chain;
    }
    strategy = _strategy;
    return err;
  };
  that.deflateSetDictionary = function(_strm, dictionary, dictLength) {
    let length = dictLength;
    let n, index = 0;
    if (!dictionary || status != INIT_STATE)
      return Z_STREAM_ERROR;
    if (length < MIN_MATCH)
      return Z_OK;
    if (length > w_size - MIN_LOOKAHEAD) {
      length = w_size - MIN_LOOKAHEAD;
      index = dictLength - length;
    }
    win.set(dictionary.subarray(index, index + length), 0);
    strstart = length;
    block_start = length;
    ins_h = win[0] & 255;
    ins_h = (ins_h << hash_shift ^ win[1] & 255) & hash_mask;
    for (n = 0; n <= length - MIN_MATCH; n++) {
      ins_h = (ins_h << hash_shift ^ win[n + (MIN_MATCH - 1)] & 255) & hash_mask;
      prev[n & w_mask] = head[ins_h];
      head[ins_h] = n;
    }
    return Z_OK;
  };
  that.deflate = function(_strm, flush) {
    let i, header, level_flags, old_flush, bstate;
    if (flush > Z_FINISH || flush < 0) {
      return Z_STREAM_ERROR;
    }
    if (!_strm.next_out || !_strm.next_in && _strm.avail_in !== 0 || status == FINISH_STATE && flush != Z_FINISH) {
      _strm.msg = z_errmsg[Z_NEED_DICT - Z_STREAM_ERROR];
      return Z_STREAM_ERROR;
    }
    if (_strm.avail_out === 0) {
      _strm.msg = z_errmsg[Z_NEED_DICT - Z_BUF_ERROR];
      return Z_BUF_ERROR;
    }
    strm = _strm;
    old_flush = last_flush;
    last_flush = flush;
    if (status == INIT_STATE) {
      header = Z_DEFLATED + (w_bits - 8 << 4) << 8;
      level_flags = (level - 1 & 255) >> 1;
      if (level_flags > 3)
        level_flags = 3;
      header |= level_flags << 6;
      if (strstart !== 0)
        header |= PRESET_DICT;
      header += 31 - header % 31;
      status = BUSY_STATE;
      putShortMSB(header);
    }
    if (that.pending !== 0) {
      strm.flush_pending();
      if (strm.avail_out === 0) {
        last_flush = -1;
        return Z_OK;
      }
    } else if (strm.avail_in === 0 && flush <= old_flush && flush != Z_FINISH) {
      strm.msg = z_errmsg[Z_NEED_DICT - Z_BUF_ERROR];
      return Z_BUF_ERROR;
    }
    if (status == FINISH_STATE && strm.avail_in !== 0) {
      _strm.msg = z_errmsg[Z_NEED_DICT - Z_BUF_ERROR];
      return Z_BUF_ERROR;
    }
    if (strm.avail_in !== 0 || lookahead !== 0 || flush != Z_NO_FLUSH && status != FINISH_STATE) {
      bstate = -1;
      switch (config_table[level].func) {
        case STORED:
          bstate = deflate_stored(flush);
          break;
        case FAST:
          bstate = deflate_fast(flush);
          break;
        case SLOW:
          bstate = deflate_slow(flush);
          break;
        default:
      }
      if (bstate == FinishStarted || bstate == FinishDone) {
        status = FINISH_STATE;
      }
      if (bstate == NeedMore || bstate == FinishStarted) {
        if (strm.avail_out === 0) {
          last_flush = -1;
        }
        return Z_OK;
      }
      if (bstate == BlockDone) {
        if (flush == Z_PARTIAL_FLUSH) {
          _tr_align();
        } else {
          _tr_stored_block(0, 0, false);
          if (flush == Z_FULL_FLUSH) {
            for (i = 0; i < hash_size; i++)
              head[i] = 0;
          }
        }
        strm.flush_pending();
        if (strm.avail_out === 0) {
          last_flush = -1;
          return Z_OK;
        }
      }
    }
    if (flush != Z_FINISH)
      return Z_OK;
    return Z_STREAM_END;
  };
}
function ZStream() {
  const that = this;
  that.next_in_index = 0;
  that.next_out_index = 0;
  that.avail_in = 0;
  that.total_in = 0;
  that.avail_out = 0;
  that.total_out = 0;
}
ZStream.prototype = {
  deflateInit(level, bits) {
    const that = this;
    that.dstate = new Deflate();
    if (!bits)
      bits = MAX_BITS;
    return that.dstate.deflateInit(that, level, bits);
  },
  deflate(flush) {
    const that = this;
    if (!that.dstate) {
      return Z_STREAM_ERROR;
    }
    return that.dstate.deflate(that, flush);
  },
  deflateEnd() {
    const that = this;
    if (!that.dstate)
      return Z_STREAM_ERROR;
    const ret = that.dstate.deflateEnd();
    that.dstate = null;
    return ret;
  },
  deflateParams(level, strategy) {
    const that = this;
    if (!that.dstate)
      return Z_STREAM_ERROR;
    return that.dstate.deflateParams(that, level, strategy);
  },
  deflateSetDictionary(dictionary, dictLength) {
    const that = this;
    if (!that.dstate)
      return Z_STREAM_ERROR;
    return that.dstate.deflateSetDictionary(that, dictionary, dictLength);
  },
  // Read a new buffer from the current input stream, update the
  // total number of bytes read. All deflate() input goes through
  // this function so some applications may wish to modify it to avoid
  // allocating a large strm->next_in buffer and copying from it.
  // (See also flush_pending()).
  read_buf(buf, start, size) {
    const that = this;
    let len = that.avail_in;
    if (len > size)
      len = size;
    if (len === 0)
      return 0;
    that.avail_in -= len;
    buf.set(that.next_in.subarray(that.next_in_index, that.next_in_index + len), start);
    that.next_in_index += len;
    that.total_in += len;
    return len;
  },
  // Flush as much pending output as possible. All deflate() output goes
  // through this function so some applications may wish to modify it
  // to avoid allocating a large strm->next_out buffer and copying into it.
  // (See also read_buf()).
  flush_pending() {
    const that = this;
    let len = that.dstate.pending;
    if (len > that.avail_out)
      len = that.avail_out;
    if (len === 0)
      return;
    that.next_out.set(that.dstate.pending_buf.subarray(that.dstate.pending_out, that.dstate.pending_out + len), that.next_out_index);
    that.next_out_index += len;
    that.dstate.pending_out += len;
    that.total_out += len;
    that.avail_out -= len;
    that.dstate.pending -= len;
    if (that.dstate.pending === 0) {
      that.dstate.pending_out = 0;
    }
  }
};
function ZipDeflate(options) {
  const that = this;
  const z = new ZStream();
  const bufsize = getMaximumCompressedSize(options && options.chunkSize ? options.chunkSize : 64 * 1024);
  const flush = Z_NO_FLUSH;
  const buf = new Uint8Array(bufsize);
  let level = options ? options.level : Z_DEFAULT_COMPRESSION;
  if (typeof level == "undefined")
    level = Z_DEFAULT_COMPRESSION;
  z.deflateInit(level);
  z.next_out = buf;
  that.append = function(data, onprogress) {
    let err, array, lastIndex = 0, bufferIndex = 0, bufferSize = 0;
    const buffers = [];
    if (!data.length)
      return;
    z.next_in_index = 0;
    z.next_in = data;
    z.avail_in = data.length;
    do {
      z.next_out_index = 0;
      z.avail_out = bufsize;
      err = z.deflate(flush);
      if (err != Z_OK)
        throw new Error("deflating: " + z.msg);
      if (z.next_out_index)
        if (z.next_out_index == bufsize)
          buffers.push(new Uint8Array(buf));
        else
          buffers.push(buf.subarray(0, z.next_out_index));
      bufferSize += z.next_out_index;
      if (onprogress && z.next_in_index > 0 && z.next_in_index != lastIndex) {
        onprogress(z.next_in_index);
        lastIndex = z.next_in_index;
      }
    } while (z.avail_in > 0 || z.avail_out === 0);
    if (buffers.length > 1) {
      array = new Uint8Array(bufferSize);
      buffers.forEach(function(chunk) {
        array.set(chunk, bufferIndex);
        bufferIndex += chunk.length;
      });
    } else {
      array = buffers[0] ? new Uint8Array(buffers[0]) : new Uint8Array();
    }
    return array;
  };
  that.flush = function() {
    let err, array, bufferIndex = 0, bufferSize = 0;
    const buffers = [];
    do {
      z.next_out_index = 0;
      z.avail_out = bufsize;
      err = z.deflate(Z_FINISH);
      if (err != Z_STREAM_END && err != Z_OK)
        throw new Error("deflating: " + z.msg);
      if (bufsize - z.avail_out > 0)
        buffers.push(buf.slice(0, z.next_out_index));
      bufferSize += z.next_out_index;
    } while (z.avail_in > 0 || z.avail_out === 0);
    z.deflateEnd();
    array = new Uint8Array(bufferSize);
    buffers.forEach(function(chunk) {
      array.set(chunk, bufferIndex);
      bufferIndex += chunk.length;
    });
    return array;
  };
}
function getMaximumCompressedSize(uncompressedSize) {
  return uncompressedSize + 5 * (Math.floor(uncompressedSize / 16383) + 1);
}

// node_modules/@zip.js/zip.js/lib/core/streams/codecs/inflate.js
var MAX_BITS2 = 15;
var Z_OK2 = 0;
var Z_STREAM_END2 = 1;
var Z_NEED_DICT2 = 2;
var Z_STREAM_ERROR2 = -2;
var Z_DATA_ERROR2 = -3;
var Z_MEM_ERROR = -4;
var Z_BUF_ERROR2 = -5;
var inflate_mask = [
  0,
  1,
  3,
  7,
  15,
  31,
  63,
  127,
  255,
  511,
  1023,
  2047,
  4095,
  8191,
  16383,
  32767,
  65535
];
var MANY = 1440;
var Z_NO_FLUSH2 = 0;
var Z_FINISH2 = 4;
var fixed_bl = 9;
var fixed_bd = 5;
var fixed_tl = [
  96,
  7,
  256,
  0,
  8,
  80,
  0,
  8,
  16,
  84,
  8,
  115,
  82,
  7,
  31,
  0,
  8,
  112,
  0,
  8,
  48,
  0,
  9,
  192,
  80,
  7,
  10,
  0,
  8,
  96,
  0,
  8,
  32,
  0,
  9,
  160,
  0,
  8,
  0,
  0,
  8,
  128,
  0,
  8,
  64,
  0,
  9,
  224,
  80,
  7,
  6,
  0,
  8,
  88,
  0,
  8,
  24,
  0,
  9,
  144,
  83,
  7,
  59,
  0,
  8,
  120,
  0,
  8,
  56,
  0,
  9,
  208,
  81,
  7,
  17,
  0,
  8,
  104,
  0,
  8,
  40,
  0,
  9,
  176,
  0,
  8,
  8,
  0,
  8,
  136,
  0,
  8,
  72,
  0,
  9,
  240,
  80,
  7,
  4,
  0,
  8,
  84,
  0,
  8,
  20,
  85,
  8,
  227,
  83,
  7,
  43,
  0,
  8,
  116,
  0,
  8,
  52,
  0,
  9,
  200,
  81,
  7,
  13,
  0,
  8,
  100,
  0,
  8,
  36,
  0,
  9,
  168,
  0,
  8,
  4,
  0,
  8,
  132,
  0,
  8,
  68,
  0,
  9,
  232,
  80,
  7,
  8,
  0,
  8,
  92,
  0,
  8,
  28,
  0,
  9,
  152,
  84,
  7,
  83,
  0,
  8,
  124,
  0,
  8,
  60,
  0,
  9,
  216,
  82,
  7,
  23,
  0,
  8,
  108,
  0,
  8,
  44,
  0,
  9,
  184,
  0,
  8,
  12,
  0,
  8,
  140,
  0,
  8,
  76,
  0,
  9,
  248,
  80,
  7,
  3,
  0,
  8,
  82,
  0,
  8,
  18,
  85,
  8,
  163,
  83,
  7,
  35,
  0,
  8,
  114,
  0,
  8,
  50,
  0,
  9,
  196,
  81,
  7,
  11,
  0,
  8,
  98,
  0,
  8,
  34,
  0,
  9,
  164,
  0,
  8,
  2,
  0,
  8,
  130,
  0,
  8,
  66,
  0,
  9,
  228,
  80,
  7,
  7,
  0,
  8,
  90,
  0,
  8,
  26,
  0,
  9,
  148,
  84,
  7,
  67,
  0,
  8,
  122,
  0,
  8,
  58,
  0,
  9,
  212,
  82,
  7,
  19,
  0,
  8,
  106,
  0,
  8,
  42,
  0,
  9,
  180,
  0,
  8,
  10,
  0,
  8,
  138,
  0,
  8,
  74,
  0,
  9,
  244,
  80,
  7,
  5,
  0,
  8,
  86,
  0,
  8,
  22,
  192,
  8,
  0,
  83,
  7,
  51,
  0,
  8,
  118,
  0,
  8,
  54,
  0,
  9,
  204,
  81,
  7,
  15,
  0,
  8,
  102,
  0,
  8,
  38,
  0,
  9,
  172,
  0,
  8,
  6,
  0,
  8,
  134,
  0,
  8,
  70,
  0,
  9,
  236,
  80,
  7,
  9,
  0,
  8,
  94,
  0,
  8,
  30,
  0,
  9,
  156,
  84,
  7,
  99,
  0,
  8,
  126,
  0,
  8,
  62,
  0,
  9,
  220,
  82,
  7,
  27,
  0,
  8,
  110,
  0,
  8,
  46,
  0,
  9,
  188,
  0,
  8,
  14,
  0,
  8,
  142,
  0,
  8,
  78,
  0,
  9,
  252,
  96,
  7,
  256,
  0,
  8,
  81,
  0,
  8,
  17,
  85,
  8,
  131,
  82,
  7,
  31,
  0,
  8,
  113,
  0,
  8,
  49,
  0,
  9,
  194,
  80,
  7,
  10,
  0,
  8,
  97,
  0,
  8,
  33,
  0,
  9,
  162,
  0,
  8,
  1,
  0,
  8,
  129,
  0,
  8,
  65,
  0,
  9,
  226,
  80,
  7,
  6,
  0,
  8,
  89,
  0,
  8,
  25,
  0,
  9,
  146,
  83,
  7,
  59,
  0,
  8,
  121,
  0,
  8,
  57,
  0,
  9,
  210,
  81,
  7,
  17,
  0,
  8,
  105,
  0,
  8,
  41,
  0,
  9,
  178,
  0,
  8,
  9,
  0,
  8,
  137,
  0,
  8,
  73,
  0,
  9,
  242,
  80,
  7,
  4,
  0,
  8,
  85,
  0,
  8,
  21,
  80,
  8,
  258,
  83,
  7,
  43,
  0,
  8,
  117,
  0,
  8,
  53,
  0,
  9,
  202,
  81,
  7,
  13,
  0,
  8,
  101,
  0,
  8,
  37,
  0,
  9,
  170,
  0,
  8,
  5,
  0,
  8,
  133,
  0,
  8,
  69,
  0,
  9,
  234,
  80,
  7,
  8,
  0,
  8,
  93,
  0,
  8,
  29,
  0,
  9,
  154,
  84,
  7,
  83,
  0,
  8,
  125,
  0,
  8,
  61,
  0,
  9,
  218,
  82,
  7,
  23,
  0,
  8,
  109,
  0,
  8,
  45,
  0,
  9,
  186,
  0,
  8,
  13,
  0,
  8,
  141,
  0,
  8,
  77,
  0,
  9,
  250,
  80,
  7,
  3,
  0,
  8,
  83,
  0,
  8,
  19,
  85,
  8,
  195,
  83,
  7,
  35,
  0,
  8,
  115,
  0,
  8,
  51,
  0,
  9,
  198,
  81,
  7,
  11,
  0,
  8,
  99,
  0,
  8,
  35,
  0,
  9,
  166,
  0,
  8,
  3,
  0,
  8,
  131,
  0,
  8,
  67,
  0,
  9,
  230,
  80,
  7,
  7,
  0,
  8,
  91,
  0,
  8,
  27,
  0,
  9,
  150,
  84,
  7,
  67,
  0,
  8,
  123,
  0,
  8,
  59,
  0,
  9,
  214,
  82,
  7,
  19,
  0,
  8,
  107,
  0,
  8,
  43,
  0,
  9,
  182,
  0,
  8,
  11,
  0,
  8,
  139,
  0,
  8,
  75,
  0,
  9,
  246,
  80,
  7,
  5,
  0,
  8,
  87,
  0,
  8,
  23,
  192,
  8,
  0,
  83,
  7,
  51,
  0,
  8,
  119,
  0,
  8,
  55,
  0,
  9,
  206,
  81,
  7,
  15,
  0,
  8,
  103,
  0,
  8,
  39,
  0,
  9,
  174,
  0,
  8,
  7,
  0,
  8,
  135,
  0,
  8,
  71,
  0,
  9,
  238,
  80,
  7,
  9,
  0,
  8,
  95,
  0,
  8,
  31,
  0,
  9,
  158,
  84,
  7,
  99,
  0,
  8,
  127,
  0,
  8,
  63,
  0,
  9,
  222,
  82,
  7,
  27,
  0,
  8,
  111,
  0,
  8,
  47,
  0,
  9,
  190,
  0,
  8,
  15,
  0,
  8,
  143,
  0,
  8,
  79,
  0,
  9,
  254,
  96,
  7,
  256,
  0,
  8,
  80,
  0,
  8,
  16,
  84,
  8,
  115,
  82,
  7,
  31,
  0,
  8,
  112,
  0,
  8,
  48,
  0,
  9,
  193,
  80,
  7,
  10,
  0,
  8,
  96,
  0,
  8,
  32,
  0,
  9,
  161,
  0,
  8,
  0,
  0,
  8,
  128,
  0,
  8,
  64,
  0,
  9,
  225,
  80,
  7,
  6,
  0,
  8,
  88,
  0,
  8,
  24,
  0,
  9,
  145,
  83,
  7,
  59,
  0,
  8,
  120,
  0,
  8,
  56,
  0,
  9,
  209,
  81,
  7,
  17,
  0,
  8,
  104,
  0,
  8,
  40,
  0,
  9,
  177,
  0,
  8,
  8,
  0,
  8,
  136,
  0,
  8,
  72,
  0,
  9,
  241,
  80,
  7,
  4,
  0,
  8,
  84,
  0,
  8,
  20,
  85,
  8,
  227,
  83,
  7,
  43,
  0,
  8,
  116,
  0,
  8,
  52,
  0,
  9,
  201,
  81,
  7,
  13,
  0,
  8,
  100,
  0,
  8,
  36,
  0,
  9,
  169,
  0,
  8,
  4,
  0,
  8,
  132,
  0,
  8,
  68,
  0,
  9,
  233,
  80,
  7,
  8,
  0,
  8,
  92,
  0,
  8,
  28,
  0,
  9,
  153,
  84,
  7,
  83,
  0,
  8,
  124,
  0,
  8,
  60,
  0,
  9,
  217,
  82,
  7,
  23,
  0,
  8,
  108,
  0,
  8,
  44,
  0,
  9,
  185,
  0,
  8,
  12,
  0,
  8,
  140,
  0,
  8,
  76,
  0,
  9,
  249,
  80,
  7,
  3,
  0,
  8,
  82,
  0,
  8,
  18,
  85,
  8,
  163,
  83,
  7,
  35,
  0,
  8,
  114,
  0,
  8,
  50,
  0,
  9,
  197,
  81,
  7,
  11,
  0,
  8,
  98,
  0,
  8,
  34,
  0,
  9,
  165,
  0,
  8,
  2,
  0,
  8,
  130,
  0,
  8,
  66,
  0,
  9,
  229,
  80,
  7,
  7,
  0,
  8,
  90,
  0,
  8,
  26,
  0,
  9,
  149,
  84,
  7,
  67,
  0,
  8,
  122,
  0,
  8,
  58,
  0,
  9,
  213,
  82,
  7,
  19,
  0,
  8,
  106,
  0,
  8,
  42,
  0,
  9,
  181,
  0,
  8,
  10,
  0,
  8,
  138,
  0,
  8,
  74,
  0,
  9,
  245,
  80,
  7,
  5,
  0,
  8,
  86,
  0,
  8,
  22,
  192,
  8,
  0,
  83,
  7,
  51,
  0,
  8,
  118,
  0,
  8,
  54,
  0,
  9,
  205,
  81,
  7,
  15,
  0,
  8,
  102,
  0,
  8,
  38,
  0,
  9,
  173,
  0,
  8,
  6,
  0,
  8,
  134,
  0,
  8,
  70,
  0,
  9,
  237,
  80,
  7,
  9,
  0,
  8,
  94,
  0,
  8,
  30,
  0,
  9,
  157,
  84,
  7,
  99,
  0,
  8,
  126,
  0,
  8,
  62,
  0,
  9,
  221,
  82,
  7,
  27,
  0,
  8,
  110,
  0,
  8,
  46,
  0,
  9,
  189,
  0,
  8,
  14,
  0,
  8,
  142,
  0,
  8,
  78,
  0,
  9,
  253,
  96,
  7,
  256,
  0,
  8,
  81,
  0,
  8,
  17,
  85,
  8,
  131,
  82,
  7,
  31,
  0,
  8,
  113,
  0,
  8,
  49,
  0,
  9,
  195,
  80,
  7,
  10,
  0,
  8,
  97,
  0,
  8,
  33,
  0,
  9,
  163,
  0,
  8,
  1,
  0,
  8,
  129,
  0,
  8,
  65,
  0,
  9,
  227,
  80,
  7,
  6,
  0,
  8,
  89,
  0,
  8,
  25,
  0,
  9,
  147,
  83,
  7,
  59,
  0,
  8,
  121,
  0,
  8,
  57,
  0,
  9,
  211,
  81,
  7,
  17,
  0,
  8,
  105,
  0,
  8,
  41,
  0,
  9,
  179,
  0,
  8,
  9,
  0,
  8,
  137,
  0,
  8,
  73,
  0,
  9,
  243,
  80,
  7,
  4,
  0,
  8,
  85,
  0,
  8,
  21,
  80,
  8,
  258,
  83,
  7,
  43,
  0,
  8,
  117,
  0,
  8,
  53,
  0,
  9,
  203,
  81,
  7,
  13,
  0,
  8,
  101,
  0,
  8,
  37,
  0,
  9,
  171,
  0,
  8,
  5,
  0,
  8,
  133,
  0,
  8,
  69,
  0,
  9,
  235,
  80,
  7,
  8,
  0,
  8,
  93,
  0,
  8,
  29,
  0,
  9,
  155,
  84,
  7,
  83,
  0,
  8,
  125,
  0,
  8,
  61,
  0,
  9,
  219,
  82,
  7,
  23,
  0,
  8,
  109,
  0,
  8,
  45,
  0,
  9,
  187,
  0,
  8,
  13,
  0,
  8,
  141,
  0,
  8,
  77,
  0,
  9,
  251,
  80,
  7,
  3,
  0,
  8,
  83,
  0,
  8,
  19,
  85,
  8,
  195,
  83,
  7,
  35,
  0,
  8,
  115,
  0,
  8,
  51,
  0,
  9,
  199,
  81,
  7,
  11,
  0,
  8,
  99,
  0,
  8,
  35,
  0,
  9,
  167,
  0,
  8,
  3,
  0,
  8,
  131,
  0,
  8,
  67,
  0,
  9,
  231,
  80,
  7,
  7,
  0,
  8,
  91,
  0,
  8,
  27,
  0,
  9,
  151,
  84,
  7,
  67,
  0,
  8,
  123,
  0,
  8,
  59,
  0,
  9,
  215,
  82,
  7,
  19,
  0,
  8,
  107,
  0,
  8,
  43,
  0,
  9,
  183,
  0,
  8,
  11,
  0,
  8,
  139,
  0,
  8,
  75,
  0,
  9,
  247,
  80,
  7,
  5,
  0,
  8,
  87,
  0,
  8,
  23,
  192,
  8,
  0,
  83,
  7,
  51,
  0,
  8,
  119,
  0,
  8,
  55,
  0,
  9,
  207,
  81,
  7,
  15,
  0,
  8,
  103,
  0,
  8,
  39,
  0,
  9,
  175,
  0,
  8,
  7,
  0,
  8,
  135,
  0,
  8,
  71,
  0,
  9,
  239,
  80,
  7,
  9,
  0,
  8,
  95,
  0,
  8,
  31,
  0,
  9,
  159,
  84,
  7,
  99,
  0,
  8,
  127,
  0,
  8,
  63,
  0,
  9,
  223,
  82,
  7,
  27,
  0,
  8,
  111,
  0,
  8,
  47,
  0,
  9,
  191,
  0,
  8,
  15,
  0,
  8,
  143,
  0,
  8,
  79,
  0,
  9,
  255
];
var fixed_td = [
  80,
  5,
  1,
  87,
  5,
  257,
  83,
  5,
  17,
  91,
  5,
  4097,
  81,
  5,
  5,
  89,
  5,
  1025,
  85,
  5,
  65,
  93,
  5,
  16385,
  80,
  5,
  3,
  88,
  5,
  513,
  84,
  5,
  33,
  92,
  5,
  8193,
  82,
  5,
  9,
  90,
  5,
  2049,
  86,
  5,
  129,
  192,
  5,
  24577,
  80,
  5,
  2,
  87,
  5,
  385,
  83,
  5,
  25,
  91,
  5,
  6145,
  81,
  5,
  7,
  89,
  5,
  1537,
  85,
  5,
  97,
  93,
  5,
  24577,
  80,
  5,
  4,
  88,
  5,
  769,
  84,
  5,
  49,
  92,
  5,
  12289,
  82,
  5,
  13,
  90,
  5,
  3073,
  86,
  5,
  193,
  192,
  5,
  24577
];
var cplens = [
  // Copy lengths for literal codes 257..285
  3,
  4,
  5,
  6,
  7,
  8,
  9,
  10,
  11,
  13,
  15,
  17,
  19,
  23,
  27,
  31,
  35,
  43,
  51,
  59,
  67,
  83,
  99,
  115,
  131,
  163,
  195,
  227,
  258,
  0,
  0
];
var cplext = [
  // Extra bits for literal codes 257..285
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  0,
  1,
  1,
  1,
  1,
  2,
  2,
  2,
  2,
  3,
  3,
  3,
  3,
  4,
  4,
  4,
  4,
  5,
  5,
  5,
  5,
  0,
  112,
  112
  // 112==invalid
];
var cpdist = [
  // Copy offsets for distance codes 0..29
  1,
  2,
  3,
  4,
  5,
  7,
  9,
  13,
  17,
  25,
  33,
  49,
  65,
  97,
  129,
  193,
  257,
  385,
  513,
  769,
  1025,
  1537,
  2049,
  3073,
  4097,
  6145,
  8193,
  12289,
  16385,
  24577
];
var cpdext = [
  // Extra bits for distance codes
  0,
  0,
  0,
  0,
  1,
  1,
  2,
  2,
  3,
  3,
  4,
  4,
  5,
  5,
  6,
  6,
  7,
  7,
  8,
  8,
  9,
  9,
  10,
  10,
  11,
  11,
  12,
  12,
  13,
  13
];
var BMAX = 15;
function InfTree() {
  const that = this;
  let hn;
  let v;
  let c;
  let r;
  let u;
  let x;
  function huft_build(b, bindex, n, s, d, e2, t, m, hp, hn2, v2) {
    let a;
    let f;
    let g;
    let h;
    let i;
    let j;
    let k;
    let l;
    let mask;
    let p;
    let q;
    let w;
    let xp;
    let y;
    let z;
    p = 0;
    i = n;
    do {
      c[b[bindex + p]]++;
      p++;
      i--;
    } while (i !== 0);
    if (c[0] == n) {
      t[0] = -1;
      m[0] = 0;
      return Z_OK2;
    }
    l = m[0];
    for (j = 1; j <= BMAX; j++)
      if (c[j] !== 0)
        break;
    k = j;
    if (l < j) {
      l = j;
    }
    for (i = BMAX; i !== 0; i--) {
      if (c[i] !== 0)
        break;
    }
    g = i;
    if (l > i) {
      l = i;
    }
    m[0] = l;
    for (y = 1 << j; j < i; j++, y <<= 1) {
      if ((y -= c[j]) < 0) {
        return Z_DATA_ERROR2;
      }
    }
    if ((y -= c[i]) < 0) {
      return Z_DATA_ERROR2;
    }
    c[i] += y;
    x[1] = j = 0;
    p = 1;
    xp = 2;
    while (--i !== 0) {
      x[xp] = j += c[p];
      xp++;
      p++;
    }
    i = 0;
    p = 0;
    do {
      if ((j = b[bindex + p]) !== 0) {
        v2[x[j]++] = i;
      }
      p++;
    } while (++i < n);
    n = x[g];
    x[0] = i = 0;
    p = 0;
    h = -1;
    w = -l;
    u[0] = 0;
    q = 0;
    z = 0;
    for (; k <= g; k++) {
      a = c[k];
      while (a-- !== 0) {
        while (k > w + l) {
          h++;
          w += l;
          z = g - w;
          z = z > l ? l : z;
          if ((f = 1 << (j = k - w)) > a + 1) {
            f -= a + 1;
            xp = k;
            if (j < z) {
              while (++j < z) {
                if ((f <<= 1) <= c[++xp])
                  break;
                f -= c[xp];
              }
            }
          }
          z = 1 << j;
          if (hn2[0] + z > MANY) {
            return Z_DATA_ERROR2;
          }
          u[h] = q = /* hp+ */
          hn2[0];
          hn2[0] += z;
          if (h !== 0) {
            x[h] = i;
            r[0] = /* (byte) */
            j;
            r[1] = /* (byte) */
            l;
            j = i >>> w - l;
            r[2] = /* (int) */
            q - u[h - 1] - j;
            hp.set(r, (u[h - 1] + j) * 3);
          } else {
            t[0] = q;
          }
        }
        r[1] = /* (byte) */
        k - w;
        if (p >= n) {
          r[0] = 128 + 64;
        } else if (v2[p] < s) {
          r[0] = /* (byte) */
          v2[p] < 256 ? 0 : 32 + 64;
          r[2] = v2[p++];
        } else {
          r[0] = /* (byte) */
          e2[v2[p] - s] + 16 + 64;
          r[2] = d[v2[p++] - s];
        }
        f = 1 << k - w;
        for (j = i >>> w; j < z; j += f) {
          hp.set(r, (q + j) * 3);
        }
        for (j = 1 << k - 1; (i & j) !== 0; j >>>= 1) {
          i ^= j;
        }
        i ^= j;
        mask = (1 << w) - 1;
        while ((i & mask) != x[h]) {
          h--;
          w -= l;
          mask = (1 << w) - 1;
        }
      }
    }
    return y !== 0 && g != 1 ? Z_BUF_ERROR2 : Z_OK2;
  }
  function initWorkArea(vsize) {
    let i;
    if (!hn) {
      hn = [];
      v = [];
      c = new Int32Array(BMAX + 1);
      r = [];
      u = new Int32Array(BMAX);
      x = new Int32Array(BMAX + 1);
    }
    if (v.length < vsize) {
      v = [];
    }
    for (i = 0; i < vsize; i++) {
      v[i] = 0;
    }
    for (i = 0; i < BMAX + 1; i++) {
      c[i] = 0;
    }
    for (i = 0; i < 3; i++) {
      r[i] = 0;
    }
    u.set(c.subarray(0, BMAX), 0);
    x.set(c.subarray(0, BMAX + 1), 0);
  }
  that.inflate_trees_bits = function(c2, bb, tb, hp, z) {
    let result;
    initWorkArea(19);
    hn[0] = 0;
    result = huft_build(c2, 0, 19, 19, null, null, tb, bb, hp, hn, v);
    if (result == Z_DATA_ERROR2) {
      z.msg = "oversubscribed dynamic bit lengths tree";
    } else if (result == Z_BUF_ERROR2 || bb[0] === 0) {
      z.msg = "incomplete dynamic bit lengths tree";
      result = Z_DATA_ERROR2;
    }
    return result;
  };
  that.inflate_trees_dynamic = function(nl, nd, c2, bl, bd, tl, td, hp, z) {
    let result;
    initWorkArea(288);
    hn[0] = 0;
    result = huft_build(c2, 0, nl, 257, cplens, cplext, tl, bl, hp, hn, v);
    if (result != Z_OK2 || bl[0] === 0) {
      if (result == Z_DATA_ERROR2) {
        z.msg = "oversubscribed literal/length tree";
      } else if (result != Z_MEM_ERROR) {
        z.msg = "incomplete literal/length tree";
        result = Z_DATA_ERROR2;
      }
      return result;
    }
    initWorkArea(288);
    result = huft_build(c2, nl, nd, 0, cpdist, cpdext, td, bd, hp, hn, v);
    if (result != Z_OK2 || bd[0] === 0 && nl > 257) {
      if (result == Z_DATA_ERROR2) {
        z.msg = "oversubscribed distance tree";
      } else if (result == Z_BUF_ERROR2) {
        z.msg = "incomplete distance tree";
        result = Z_DATA_ERROR2;
      } else if (result != Z_MEM_ERROR) {
        z.msg = "empty distance tree with lengths";
        result = Z_DATA_ERROR2;
      }
      return result;
    }
    return Z_OK2;
  };
}
InfTree.inflate_trees_fixed = function(bl, bd, tl, td) {
  bl[0] = fixed_bl;
  bd[0] = fixed_bd;
  tl[0] = fixed_tl;
  td[0] = fixed_td;
  return Z_OK2;
};
var START = 0;
var LEN = 1;
var LENEXT = 2;
var DIST = 3;
var DISTEXT = 4;
var COPY = 5;
var LIT = 6;
var WASH = 7;
var END = 8;
var BADCODE = 9;
function InfCodes() {
  const that = this;
  let mode2;
  let len = 0;
  let tree;
  let tree_index = 0;
  let need = 0;
  let lit = 0;
  let get = 0;
  let dist = 0;
  let lbits = 0;
  let dbits = 0;
  let ltree;
  let ltree_index = 0;
  let dtree;
  let dtree_index = 0;
  function inflate_fast(bl, bd, tl, tl_index, td, td_index, s, z) {
    let t;
    let tp;
    let tp_index;
    let e2;
    let b;
    let k;
    let p;
    let n;
    let q;
    let m;
    let ml;
    let md;
    let c;
    let d;
    let r;
    let tp_index_t_3;
    p = z.next_in_index;
    n = z.avail_in;
    b = s.bitb;
    k = s.bitk;
    q = s.write;
    m = q < s.read ? s.read - q - 1 : s.end - q;
    ml = inflate_mask[bl];
    md = inflate_mask[bd];
    do {
      while (k < 20) {
        n--;
        b |= (z.read_byte(p++) & 255) << k;
        k += 8;
      }
      t = b & ml;
      tp = tl;
      tp_index = tl_index;
      tp_index_t_3 = (tp_index + t) * 3;
      if ((e2 = tp[tp_index_t_3]) === 0) {
        b >>= tp[tp_index_t_3 + 1];
        k -= tp[tp_index_t_3 + 1];
        s.win[q++] = /* (byte) */
        tp[tp_index_t_3 + 2];
        m--;
        continue;
      }
      do {
        b >>= tp[tp_index_t_3 + 1];
        k -= tp[tp_index_t_3 + 1];
        if ((e2 & 16) !== 0) {
          e2 &= 15;
          c = tp[tp_index_t_3 + 2] + /* (int) */
          (b & inflate_mask[e2]);
          b >>= e2;
          k -= e2;
          while (k < 15) {
            n--;
            b |= (z.read_byte(p++) & 255) << k;
            k += 8;
          }
          t = b & md;
          tp = td;
          tp_index = td_index;
          tp_index_t_3 = (tp_index + t) * 3;
          e2 = tp[tp_index_t_3];
          do {
            b >>= tp[tp_index_t_3 + 1];
            k -= tp[tp_index_t_3 + 1];
            if ((e2 & 16) !== 0) {
              e2 &= 15;
              while (k < e2) {
                n--;
                b |= (z.read_byte(p++) & 255) << k;
                k += 8;
              }
              d = tp[tp_index_t_3 + 2] + (b & inflate_mask[e2]);
              b >>= e2;
              k -= e2;
              m -= c;
              if (q >= d) {
                r = q - d;
                if (q - r > 0 && 2 > q - r) {
                  s.win[q++] = s.win[r++];
                  s.win[q++] = s.win[r++];
                  c -= 2;
                } else {
                  s.win.set(s.win.subarray(r, r + 2), q);
                  q += 2;
                  r += 2;
                  c -= 2;
                }
              } else {
                r = q - d;
                do {
                  r += s.end;
                } while (r < 0);
                e2 = s.end - r;
                if (c > e2) {
                  c -= e2;
                  if (q - r > 0 && e2 > q - r) {
                    do {
                      s.win[q++] = s.win[r++];
                    } while (--e2 !== 0);
                  } else {
                    s.win.set(s.win.subarray(r, r + e2), q);
                    q += e2;
                    r += e2;
                    e2 = 0;
                  }
                  r = 0;
                }
              }
              if (q - r > 0 && c > q - r) {
                do {
                  s.win[q++] = s.win[r++];
                } while (--c !== 0);
              } else {
                s.win.set(s.win.subarray(r, r + c), q);
                q += c;
                r += c;
                c = 0;
              }
              break;
            } else if ((e2 & 64) === 0) {
              t += tp[tp_index_t_3 + 2];
              t += b & inflate_mask[e2];
              tp_index_t_3 = (tp_index + t) * 3;
              e2 = tp[tp_index_t_3];
            } else {
              z.msg = "invalid distance code";
              c = z.avail_in - n;
              c = k >> 3 < c ? k >> 3 : c;
              n += c;
              p -= c;
              k -= c << 3;
              s.bitb = b;
              s.bitk = k;
              z.avail_in = n;
              z.total_in += p - z.next_in_index;
              z.next_in_index = p;
              s.write = q;
              return Z_DATA_ERROR2;
            }
          } while (true);
          break;
        }
        if ((e2 & 64) === 0) {
          t += tp[tp_index_t_3 + 2];
          t += b & inflate_mask[e2];
          tp_index_t_3 = (tp_index + t) * 3;
          if ((e2 = tp[tp_index_t_3]) === 0) {
            b >>= tp[tp_index_t_3 + 1];
            k -= tp[tp_index_t_3 + 1];
            s.win[q++] = /* (byte) */
            tp[tp_index_t_3 + 2];
            m--;
            break;
          }
        } else if ((e2 & 32) !== 0) {
          c = z.avail_in - n;
          c = k >> 3 < c ? k >> 3 : c;
          n += c;
          p -= c;
          k -= c << 3;
          s.bitb = b;
          s.bitk = k;
          z.avail_in = n;
          z.total_in += p - z.next_in_index;
          z.next_in_index = p;
          s.write = q;
          return Z_STREAM_END2;
        } else {
          z.msg = "invalid literal/length code";
          c = z.avail_in - n;
          c = k >> 3 < c ? k >> 3 : c;
          n += c;
          p -= c;
          k -= c << 3;
          s.bitb = b;
          s.bitk = k;
          z.avail_in = n;
          z.total_in += p - z.next_in_index;
          z.next_in_index = p;
          s.write = q;
          return Z_DATA_ERROR2;
        }
      } while (true);
    } while (m >= 258 && n >= 10);
    c = z.avail_in - n;
    c = k >> 3 < c ? k >> 3 : c;
    n += c;
    p -= c;
    k -= c << 3;
    s.bitb = b;
    s.bitk = k;
    z.avail_in = n;
    z.total_in += p - z.next_in_index;
    z.next_in_index = p;
    s.write = q;
    return Z_OK2;
  }
  that.init = function(bl, bd, tl, tl_index, td, td_index) {
    mode2 = START;
    lbits = /* (byte) */
    bl;
    dbits = /* (byte) */
    bd;
    ltree = tl;
    ltree_index = tl_index;
    dtree = td;
    dtree_index = td_index;
    tree = null;
  };
  that.proc = function(s, z, r) {
    let j;
    let tindex;
    let e2;
    let b = 0;
    let k = 0;
    let p = 0;
    let n;
    let q;
    let m;
    let f;
    p = z.next_in_index;
    n = z.avail_in;
    b = s.bitb;
    k = s.bitk;
    q = s.write;
    m = q < s.read ? s.read - q - 1 : s.end - q;
    while (true) {
      switch (mode2) {
        // waiting for "i:"=input, "o:"=output, "x:"=nothing
        case START:
          if (m >= 258 && n >= 10) {
            s.bitb = b;
            s.bitk = k;
            z.avail_in = n;
            z.total_in += p - z.next_in_index;
            z.next_in_index = p;
            s.write = q;
            r = inflate_fast(lbits, dbits, ltree, ltree_index, dtree, dtree_index, s, z);
            p = z.next_in_index;
            n = z.avail_in;
            b = s.bitb;
            k = s.bitk;
            q = s.write;
            m = q < s.read ? s.read - q - 1 : s.end - q;
            if (r != Z_OK2) {
              mode2 = r == Z_STREAM_END2 ? WASH : BADCODE;
              break;
            }
          }
          need = lbits;
          tree = ltree;
          tree_index = ltree_index;
          mode2 = LEN;
        /* falls through */
        case LEN:
          j = need;
          while (k < j) {
            if (n !== 0)
              r = Z_OK2;
            else {
              s.bitb = b;
              s.bitk = k;
              z.avail_in = n;
              z.total_in += p - z.next_in_index;
              z.next_in_index = p;
              s.write = q;
              return s.inflate_flush(z, r);
            }
            n--;
            b |= (z.read_byte(p++) & 255) << k;
            k += 8;
          }
          tindex = (tree_index + (b & inflate_mask[j])) * 3;
          b >>>= tree[tindex + 1];
          k -= tree[tindex + 1];
          e2 = tree[tindex];
          if (e2 === 0) {
            lit = tree[tindex + 2];
            mode2 = LIT;
            break;
          }
          if ((e2 & 16) !== 0) {
            get = e2 & 15;
            len = tree[tindex + 2];
            mode2 = LENEXT;
            break;
          }
          if ((e2 & 64) === 0) {
            need = e2;
            tree_index = tindex / 3 + tree[tindex + 2];
            break;
          }
          if ((e2 & 32) !== 0) {
            mode2 = WASH;
            break;
          }
          mode2 = BADCODE;
          z.msg = "invalid literal/length code";
          r = Z_DATA_ERROR2;
          s.bitb = b;
          s.bitk = k;
          z.avail_in = n;
          z.total_in += p - z.next_in_index;
          z.next_in_index = p;
          s.write = q;
          return s.inflate_flush(z, r);
        case LENEXT:
          j = get;
          while (k < j) {
            if (n !== 0)
              r = Z_OK2;
            else {
              s.bitb = b;
              s.bitk = k;
              z.avail_in = n;
              z.total_in += p - z.next_in_index;
              z.next_in_index = p;
              s.write = q;
              return s.inflate_flush(z, r);
            }
            n--;
            b |= (z.read_byte(p++) & 255) << k;
            k += 8;
          }
          len += b & inflate_mask[j];
          b >>= j;
          k -= j;
          need = dbits;
          tree = dtree;
          tree_index = dtree_index;
          mode2 = DIST;
        /* falls through */
        case DIST:
          j = need;
          while (k < j) {
            if (n !== 0)
              r = Z_OK2;
            else {
              s.bitb = b;
              s.bitk = k;
              z.avail_in = n;
              z.total_in += p - z.next_in_index;
              z.next_in_index = p;
              s.write = q;
              return s.inflate_flush(z, r);
            }
            n--;
            b |= (z.read_byte(p++) & 255) << k;
            k += 8;
          }
          tindex = (tree_index + (b & inflate_mask[j])) * 3;
          b >>= tree[tindex + 1];
          k -= tree[tindex + 1];
          e2 = tree[tindex];
          if ((e2 & 16) !== 0) {
            get = e2 & 15;
            dist = tree[tindex + 2];
            mode2 = DISTEXT;
            break;
          }
          if ((e2 & 64) === 0) {
            need = e2;
            tree_index = tindex / 3 + tree[tindex + 2];
            break;
          }
          mode2 = BADCODE;
          z.msg = "invalid distance code";
          r = Z_DATA_ERROR2;
          s.bitb = b;
          s.bitk = k;
          z.avail_in = n;
          z.total_in += p - z.next_in_index;
          z.next_in_index = p;
          s.write = q;
          return s.inflate_flush(z, r);
        case DISTEXT:
          j = get;
          while (k < j) {
            if (n !== 0)
              r = Z_OK2;
            else {
              s.bitb = b;
              s.bitk = k;
              z.avail_in = n;
              z.total_in += p - z.next_in_index;
              z.next_in_index = p;
              s.write = q;
              return s.inflate_flush(z, r);
            }
            n--;
            b |= (z.read_byte(p++) & 255) << k;
            k += 8;
          }
          dist += b & inflate_mask[j];
          b >>= j;
          k -= j;
          mode2 = COPY;
        /* falls through */
        case COPY:
          f = q - dist;
          while (f < 0) {
            f += s.end;
          }
          while (len !== 0) {
            if (m === 0) {
              if (q == s.end && s.read !== 0) {
                q = 0;
                m = q < s.read ? s.read - q - 1 : s.end - q;
              }
              if (m === 0) {
                s.write = q;
                r = s.inflate_flush(z, r);
                q = s.write;
                m = q < s.read ? s.read - q - 1 : s.end - q;
                if (q == s.end && s.read !== 0) {
                  q = 0;
                  m = q < s.read ? s.read - q - 1 : s.end - q;
                }
                if (m === 0) {
                  s.bitb = b;
                  s.bitk = k;
                  z.avail_in = n;
                  z.total_in += p - z.next_in_index;
                  z.next_in_index = p;
                  s.write = q;
                  return s.inflate_flush(z, r);
                }
              }
            }
            s.win[q++] = s.win[f++];
            m--;
            if (f == s.end)
              f = 0;
            len--;
          }
          mode2 = START;
          break;
        case LIT:
          if (m === 0) {
            if (q == s.end && s.read !== 0) {
              q = 0;
              m = q < s.read ? s.read - q - 1 : s.end - q;
            }
            if (m === 0) {
              s.write = q;
              r = s.inflate_flush(z, r);
              q = s.write;
              m = q < s.read ? s.read - q - 1 : s.end - q;
              if (q == s.end && s.read !== 0) {
                q = 0;
                m = q < s.read ? s.read - q - 1 : s.end - q;
              }
              if (m === 0) {
                s.bitb = b;
                s.bitk = k;
                z.avail_in = n;
                z.total_in += p - z.next_in_index;
                z.next_in_index = p;
                s.write = q;
                return s.inflate_flush(z, r);
              }
            }
          }
          r = Z_OK2;
          s.win[q++] = /* (byte) */
          lit;
          m--;
          mode2 = START;
          break;
        case WASH:
          if (k > 7) {
            k -= 8;
            n++;
            p--;
          }
          s.write = q;
          r = s.inflate_flush(z, r);
          q = s.write;
          m = q < s.read ? s.read - q - 1 : s.end - q;
          if (s.read != s.write) {
            s.bitb = b;
            s.bitk = k;
            z.avail_in = n;
            z.total_in += p - z.next_in_index;
            z.next_in_index = p;
            s.write = q;
            return s.inflate_flush(z, r);
          }
          mode2 = END;
        /* falls through */
        case END:
          r = Z_STREAM_END2;
          s.bitb = b;
          s.bitk = k;
          z.avail_in = n;
          z.total_in += p - z.next_in_index;
          z.next_in_index = p;
          s.write = q;
          return s.inflate_flush(z, r);
        case BADCODE:
          r = Z_DATA_ERROR2;
          s.bitb = b;
          s.bitk = k;
          z.avail_in = n;
          z.total_in += p - z.next_in_index;
          z.next_in_index = p;
          s.write = q;
          return s.inflate_flush(z, r);
        default:
          r = Z_STREAM_ERROR2;
          s.bitb = b;
          s.bitk = k;
          z.avail_in = n;
          z.total_in += p - z.next_in_index;
          z.next_in_index = p;
          s.write = q;
          return s.inflate_flush(z, r);
      }
    }
  };
  that.free = function() {
  };
}
var border = [
  // Order of the bit length code lengths
  16,
  17,
  18,
  0,
  8,
  7,
  9,
  6,
  10,
  5,
  11,
  4,
  12,
  3,
  13,
  2,
  14,
  1,
  15
];
var TYPE = 0;
var LENS = 1;
var STORED2 = 2;
var TABLE = 3;
var BTREE = 4;
var DTREE = 5;
var CODES = 6;
var DRY = 7;
var DONELOCKS = 8;
var BADBLOCKS = 9;
function InfBlocks(z, w) {
  const that = this;
  let mode2 = TYPE;
  let left = 0;
  let table3 = 0;
  let index = 0;
  let blens;
  const bb = [0];
  const tb = [0];
  const codes = new InfCodes();
  let last = 0;
  let hufts = new Int32Array(MANY * 3);
  const check = 0;
  const inftree = new InfTree();
  that.bitk = 0;
  that.bitb = 0;
  that.win = new Uint8Array(w);
  that.end = w;
  that.read = 0;
  that.write = 0;
  that.reset = function(z2, c) {
    if (c)
      c[0] = check;
    if (mode2 == CODES) {
      codes.free(z2);
    }
    mode2 = TYPE;
    that.bitk = 0;
    that.bitb = 0;
    that.read = that.write = 0;
  };
  that.reset(z, null);
  that.inflate_flush = function(z2, r) {
    let n;
    let p;
    let q;
    p = z2.next_out_index;
    q = that.read;
    n = /* (int) */
    (q <= that.write ? that.write : that.end) - q;
    if (n > z2.avail_out)
      n = z2.avail_out;
    if (n !== 0 && r == Z_BUF_ERROR2)
      r = Z_OK2;
    z2.avail_out -= n;
    z2.total_out += n;
    z2.next_out.set(that.win.subarray(q, q + n), p);
    p += n;
    q += n;
    if (q == that.end) {
      q = 0;
      if (that.write == that.end)
        that.write = 0;
      n = that.write - q;
      if (n > z2.avail_out)
        n = z2.avail_out;
      if (n !== 0 && r == Z_BUF_ERROR2)
        r = Z_OK2;
      z2.avail_out -= n;
      z2.total_out += n;
      z2.next_out.set(that.win.subarray(q, q + n), p);
      p += n;
      q += n;
    }
    z2.next_out_index = p;
    that.read = q;
    return r;
  };
  that.proc = function(z2, r) {
    let t;
    let b;
    let k;
    let p;
    let n;
    let q;
    let m;
    let i;
    p = z2.next_in_index;
    n = z2.avail_in;
    b = that.bitb;
    k = that.bitk;
    q = that.write;
    m = /* (int) */
    q < that.read ? that.read - q - 1 : that.end - q;
    while (true) {
      let bl, bd, tl, td, bl_, bd_, tl_, td_;
      switch (mode2) {
        case TYPE:
          while (k < 3) {
            if (n !== 0) {
              r = Z_OK2;
            } else {
              that.bitb = b;
              that.bitk = k;
              z2.avail_in = n;
              z2.total_in += p - z2.next_in_index;
              z2.next_in_index = p;
              that.write = q;
              return that.inflate_flush(z2, r);
            }
            n--;
            b |= (z2.read_byte(p++) & 255) << k;
            k += 8;
          }
          t = /* (int) */
          b & 7;
          last = t & 1;
          switch (t >>> 1) {
            case 0:
              b >>>= 3;
              k -= 3;
              t = k & 7;
              b >>>= t;
              k -= t;
              mode2 = LENS;
              break;
            case 1:
              bl = [];
              bd = [];
              tl = [[]];
              td = [[]];
              InfTree.inflate_trees_fixed(bl, bd, tl, td);
              codes.init(bl[0], bd[0], tl[0], 0, td[0], 0);
              b >>>= 3;
              k -= 3;
              mode2 = CODES;
              break;
            case 2:
              b >>>= 3;
              k -= 3;
              mode2 = TABLE;
              break;
            case 3:
              b >>>= 3;
              k -= 3;
              mode2 = BADBLOCKS;
              z2.msg = "invalid block type";
              r = Z_DATA_ERROR2;
              that.bitb = b;
              that.bitk = k;
              z2.avail_in = n;
              z2.total_in += p - z2.next_in_index;
              z2.next_in_index = p;
              that.write = q;
              return that.inflate_flush(z2, r);
          }
          break;
        case LENS:
          while (k < 32) {
            if (n !== 0) {
              r = Z_OK2;
            } else {
              that.bitb = b;
              that.bitk = k;
              z2.avail_in = n;
              z2.total_in += p - z2.next_in_index;
              z2.next_in_index = p;
              that.write = q;
              return that.inflate_flush(z2, r);
            }
            n--;
            b |= (z2.read_byte(p++) & 255) << k;
            k += 8;
          }
          if ((~b >>> 16 & 65535) != (b & 65535)) {
            mode2 = BADBLOCKS;
            z2.msg = "invalid stored block lengths";
            r = Z_DATA_ERROR2;
            that.bitb = b;
            that.bitk = k;
            z2.avail_in = n;
            z2.total_in += p - z2.next_in_index;
            z2.next_in_index = p;
            that.write = q;
            return that.inflate_flush(z2, r);
          }
          left = b & 65535;
          b = k = 0;
          mode2 = left !== 0 ? STORED2 : last !== 0 ? DRY : TYPE;
          break;
        case STORED2:
          if (n === 0) {
            that.bitb = b;
            that.bitk = k;
            z2.avail_in = n;
            z2.total_in += p - z2.next_in_index;
            z2.next_in_index = p;
            that.write = q;
            return that.inflate_flush(z2, r);
          }
          if (m === 0) {
            if (q == that.end && that.read !== 0) {
              q = 0;
              m = /* (int) */
              q < that.read ? that.read - q - 1 : that.end - q;
            }
            if (m === 0) {
              that.write = q;
              r = that.inflate_flush(z2, r);
              q = that.write;
              m = /* (int) */
              q < that.read ? that.read - q - 1 : that.end - q;
              if (q == that.end && that.read !== 0) {
                q = 0;
                m = /* (int) */
                q < that.read ? that.read - q - 1 : that.end - q;
              }
              if (m === 0) {
                that.bitb = b;
                that.bitk = k;
                z2.avail_in = n;
                z2.total_in += p - z2.next_in_index;
                z2.next_in_index = p;
                that.write = q;
                return that.inflate_flush(z2, r);
              }
            }
          }
          r = Z_OK2;
          t = left;
          if (t > n)
            t = n;
          if (t > m)
            t = m;
          that.win.set(z2.read_buf(p, t), q);
          p += t;
          n -= t;
          q += t;
          m -= t;
          if ((left -= t) !== 0)
            break;
          mode2 = last !== 0 ? DRY : TYPE;
          break;
        case TABLE:
          while (k < 14) {
            if (n !== 0) {
              r = Z_OK2;
            } else {
              that.bitb = b;
              that.bitk = k;
              z2.avail_in = n;
              z2.total_in += p - z2.next_in_index;
              z2.next_in_index = p;
              that.write = q;
              return that.inflate_flush(z2, r);
            }
            n--;
            b |= (z2.read_byte(p++) & 255) << k;
            k += 8;
          }
          table3 = t = b & 16383;
          if ((t & 31) > 29 || (t >> 5 & 31) > 29) {
            mode2 = BADBLOCKS;
            z2.msg = "too many length or distance symbols";
            r = Z_DATA_ERROR2;
            that.bitb = b;
            that.bitk = k;
            z2.avail_in = n;
            z2.total_in += p - z2.next_in_index;
            z2.next_in_index = p;
            that.write = q;
            return that.inflate_flush(z2, r);
          }
          t = 258 + (t & 31) + (t >> 5 & 31);
          if (!blens || blens.length < t) {
            blens = [];
          } else {
            for (i = 0; i < t; i++) {
              blens[i] = 0;
            }
          }
          b >>>= 14;
          k -= 14;
          index = 0;
          mode2 = BTREE;
        /* falls through */
        case BTREE:
          while (index < 4 + (table3 >>> 10)) {
            while (k < 3) {
              if (n !== 0) {
                r = Z_OK2;
              } else {
                that.bitb = b;
                that.bitk = k;
                z2.avail_in = n;
                z2.total_in += p - z2.next_in_index;
                z2.next_in_index = p;
                that.write = q;
                return that.inflate_flush(z2, r);
              }
              n--;
              b |= (z2.read_byte(p++) & 255) << k;
              k += 8;
            }
            blens[border[index++]] = b & 7;
            b >>>= 3;
            k -= 3;
          }
          while (index < 19) {
            blens[border[index++]] = 0;
          }
          bb[0] = 7;
          t = inftree.inflate_trees_bits(blens, bb, tb, hufts, z2);
          if (t != Z_OK2) {
            r = t;
            if (r == Z_DATA_ERROR2) {
              blens = null;
              mode2 = BADBLOCKS;
            }
            that.bitb = b;
            that.bitk = k;
            z2.avail_in = n;
            z2.total_in += p - z2.next_in_index;
            z2.next_in_index = p;
            that.write = q;
            return that.inflate_flush(z2, r);
          }
          index = 0;
          mode2 = DTREE;
        /* falls through */
        case DTREE:
          while (true) {
            t = table3;
            if (index >= 258 + (t & 31) + (t >> 5 & 31)) {
              break;
            }
            let j, c;
            t = bb[0];
            while (k < t) {
              if (n !== 0) {
                r = Z_OK2;
              } else {
                that.bitb = b;
                that.bitk = k;
                z2.avail_in = n;
                z2.total_in += p - z2.next_in_index;
                z2.next_in_index = p;
                that.write = q;
                return that.inflate_flush(z2, r);
              }
              n--;
              b |= (z2.read_byte(p++) & 255) << k;
              k += 8;
            }
            t = hufts[(tb[0] + (b & inflate_mask[t])) * 3 + 1];
            c = hufts[(tb[0] + (b & inflate_mask[t])) * 3 + 2];
            if (c < 16) {
              b >>>= t;
              k -= t;
              blens[index++] = c;
            } else {
              i = c == 18 ? 7 : c - 14;
              j = c == 18 ? 11 : 3;
              while (k < t + i) {
                if (n !== 0) {
                  r = Z_OK2;
                } else {
                  that.bitb = b;
                  that.bitk = k;
                  z2.avail_in = n;
                  z2.total_in += p - z2.next_in_index;
                  z2.next_in_index = p;
                  that.write = q;
                  return that.inflate_flush(z2, r);
                }
                n--;
                b |= (z2.read_byte(p++) & 255) << k;
                k += 8;
              }
              b >>>= t;
              k -= t;
              j += b & inflate_mask[i];
              b >>>= i;
              k -= i;
              i = index;
              t = table3;
              if (i + j > 258 + (t & 31) + (t >> 5 & 31) || c == 16 && i < 1) {
                blens = null;
                mode2 = BADBLOCKS;
                z2.msg = "invalid bit length repeat";
                r = Z_DATA_ERROR2;
                that.bitb = b;
                that.bitk = k;
                z2.avail_in = n;
                z2.total_in += p - z2.next_in_index;
                z2.next_in_index = p;
                that.write = q;
                return that.inflate_flush(z2, r);
              }
              c = c == 16 ? blens[i - 1] : 0;
              do {
                blens[i++] = c;
              } while (--j !== 0);
              index = i;
            }
          }
          tb[0] = -1;
          bl_ = [];
          bd_ = [];
          tl_ = [];
          td_ = [];
          bl_[0] = 9;
          bd_[0] = 6;
          t = table3;
          t = inftree.inflate_trees_dynamic(257 + (t & 31), 1 + (t >> 5 & 31), blens, bl_, bd_, tl_, td_, hufts, z2);
          if (t != Z_OK2) {
            if (t == Z_DATA_ERROR2) {
              blens = null;
              mode2 = BADBLOCKS;
            }
            r = t;
            that.bitb = b;
            that.bitk = k;
            z2.avail_in = n;
            z2.total_in += p - z2.next_in_index;
            z2.next_in_index = p;
            that.write = q;
            return that.inflate_flush(z2, r);
          }
          codes.init(bl_[0], bd_[0], hufts, tl_[0], hufts, td_[0]);
          mode2 = CODES;
        /* falls through */
        case CODES:
          that.bitb = b;
          that.bitk = k;
          z2.avail_in = n;
          z2.total_in += p - z2.next_in_index;
          z2.next_in_index = p;
          that.write = q;
          if ((r = codes.proc(that, z2, r)) != Z_STREAM_END2) {
            return that.inflate_flush(z2, r);
          }
          r = Z_OK2;
          codes.free(z2);
          p = z2.next_in_index;
          n = z2.avail_in;
          b = that.bitb;
          k = that.bitk;
          q = that.write;
          m = /* (int) */
          q < that.read ? that.read - q - 1 : that.end - q;
          if (last === 0) {
            mode2 = TYPE;
            break;
          }
          mode2 = DRY;
        /* falls through */
        case DRY:
          that.write = q;
          r = that.inflate_flush(z2, r);
          q = that.write;
          m = /* (int) */
          q < that.read ? that.read - q - 1 : that.end - q;
          if (that.read != that.write) {
            that.bitb = b;
            that.bitk = k;
            z2.avail_in = n;
            z2.total_in += p - z2.next_in_index;
            z2.next_in_index = p;
            that.write = q;
            return that.inflate_flush(z2, r);
          }
          mode2 = DONELOCKS;
        /* falls through */
        case DONELOCKS:
          r = Z_STREAM_END2;
          that.bitb = b;
          that.bitk = k;
          z2.avail_in = n;
          z2.total_in += p - z2.next_in_index;
          z2.next_in_index = p;
          that.write = q;
          return that.inflate_flush(z2, r);
        case BADBLOCKS:
          r = Z_DATA_ERROR2;
          that.bitb = b;
          that.bitk = k;
          z2.avail_in = n;
          z2.total_in += p - z2.next_in_index;
          z2.next_in_index = p;
          that.write = q;
          return that.inflate_flush(z2, r);
        default:
          r = Z_STREAM_ERROR2;
          that.bitb = b;
          that.bitk = k;
          z2.avail_in = n;
          z2.total_in += p - z2.next_in_index;
          z2.next_in_index = p;
          that.write = q;
          return that.inflate_flush(z2, r);
      }
    }
  };
  that.free = function(z2) {
    that.reset(z2, null);
    that.win = null;
    hufts = null;
  };
  that.set_dictionary = function(d, start, n) {
    that.win.set(d.subarray(start, start + n), 0);
    that.read = that.write = n;
  };
  that.sync_point = function() {
    return mode2 == LENS ? 1 : 0;
  };
}
var PRESET_DICT2 = 32;
var Z_DEFLATED2 = 8;
var METHOD = 0;
var FLAG = 1;
var DICT4 = 2;
var DICT3 = 3;
var DICT2 = 4;
var DICT1 = 5;
var DICT0 = 6;
var BLOCKS = 7;
var DONE = 12;
var BAD = 13;
var mark = [0, 0, 255, 255];
function Inflate() {
  const that = this;
  that.mode = 0;
  that.method = 0;
  that.was = [0];
  that.need = 0;
  that.marker = 0;
  that.wbits = 0;
  function inflateReset(z) {
    if (!z || !z.istate)
      return Z_STREAM_ERROR2;
    z.total_in = z.total_out = 0;
    z.msg = null;
    z.istate.mode = BLOCKS;
    z.istate.blocks.reset(z, null);
    return Z_OK2;
  }
  that.inflateEnd = function(z) {
    if (that.blocks)
      that.blocks.free(z);
    that.blocks = null;
    return Z_OK2;
  };
  that.inflateInit = function(z, w) {
    z.msg = null;
    that.blocks = null;
    if (w < 8 || w > 15) {
      that.inflateEnd(z);
      return Z_STREAM_ERROR2;
    }
    that.wbits = w;
    z.istate.blocks = new InfBlocks(z, 1 << w);
    inflateReset(z);
    return Z_OK2;
  };
  that.inflate = function(z, f) {
    let r;
    let b;
    if (!z || !z.istate || !z.next_in)
      return Z_STREAM_ERROR2;
    const istate = z.istate;
    f = f == Z_FINISH2 ? Z_BUF_ERROR2 : Z_OK2;
    r = Z_BUF_ERROR2;
    while (true) {
      switch (istate.mode) {
        case METHOD:
          if (z.avail_in === 0)
            return r;
          r = f;
          z.avail_in--;
          z.total_in++;
          if (((istate.method = z.read_byte(z.next_in_index++)) & 15) != Z_DEFLATED2) {
            istate.mode = BAD;
            z.msg = "unknown compression method";
            istate.marker = 5;
            break;
          }
          if ((istate.method >> 4) + 8 > istate.wbits) {
            istate.mode = BAD;
            z.msg = "invalid win size";
            istate.marker = 5;
            break;
          }
          istate.mode = FLAG;
        /* falls through */
        case FLAG:
          if (z.avail_in === 0)
            return r;
          r = f;
          z.avail_in--;
          z.total_in++;
          b = z.read_byte(z.next_in_index++) & 255;
          if (((istate.method << 8) + b) % 31 !== 0) {
            istate.mode = BAD;
            z.msg = "incorrect header check";
            istate.marker = 5;
            break;
          }
          if ((b & PRESET_DICT2) === 0) {
            istate.mode = BLOCKS;
            break;
          }
          istate.mode = DICT4;
        /* falls through */
        case DICT4:
          if (z.avail_in === 0)
            return r;
          r = f;
          z.avail_in--;
          z.total_in++;
          istate.need = (z.read_byte(z.next_in_index++) & 255) << 24 & 4278190080;
          istate.mode = DICT3;
        /* falls through */
        case DICT3:
          if (z.avail_in === 0)
            return r;
          r = f;
          z.avail_in--;
          z.total_in++;
          istate.need += (z.read_byte(z.next_in_index++) & 255) << 16 & 16711680;
          istate.mode = DICT2;
        /* falls through */
        case DICT2:
          if (z.avail_in === 0)
            return r;
          r = f;
          z.avail_in--;
          z.total_in++;
          istate.need += (z.read_byte(z.next_in_index++) & 255) << 8 & 65280;
          istate.mode = DICT1;
        /* falls through */
        case DICT1:
          if (z.avail_in === 0)
            return r;
          r = f;
          z.avail_in--;
          z.total_in++;
          istate.need += z.read_byte(z.next_in_index++) & 255;
          istate.mode = DICT0;
          return Z_NEED_DICT2;
        case DICT0:
          istate.mode = BAD;
          z.msg = "need dictionary";
          istate.marker = 0;
          return Z_STREAM_ERROR2;
        case BLOCKS:
          r = istate.blocks.proc(z, r);
          if (r == Z_DATA_ERROR2) {
            istate.mode = BAD;
            istate.marker = 0;
            break;
          }
          if (r == Z_OK2) {
            r = f;
          }
          if (r != Z_STREAM_END2) {
            return r;
          }
          r = f;
          istate.blocks.reset(z, istate.was);
          istate.mode = DONE;
        /* falls through */
        case DONE:
          z.avail_in = 0;
          return Z_STREAM_END2;
        case BAD:
          return Z_DATA_ERROR2;
        default:
          return Z_STREAM_ERROR2;
      }
    }
  };
  that.inflateSetDictionary = function(z, dictionary, dictLength) {
    let index = 0, length = dictLength;
    if (!z || !z.istate || z.istate.mode != DICT0)
      return Z_STREAM_ERROR2;
    const istate = z.istate;
    if (length >= 1 << istate.wbits) {
      length = (1 << istate.wbits) - 1;
      index = dictLength - length;
    }
    istate.blocks.set_dictionary(dictionary, index, length);
    istate.mode = BLOCKS;
    return Z_OK2;
  };
  that.inflateSync = function(z) {
    let n;
    let p;
    let m;
    let r, w;
    if (!z || !z.istate)
      return Z_STREAM_ERROR2;
    const istate = z.istate;
    if (istate.mode != BAD) {
      istate.mode = BAD;
      istate.marker = 0;
    }
    if ((n = z.avail_in) === 0)
      return Z_BUF_ERROR2;
    p = z.next_in_index;
    m = istate.marker;
    while (n !== 0 && m < 4) {
      if (z.read_byte(p) == mark[m]) {
        m++;
      } else if (z.read_byte(p) !== 0) {
        m = 0;
      } else {
        m = 4 - m;
      }
      p++;
      n--;
    }
    z.total_in += p - z.next_in_index;
    z.next_in_index = p;
    z.avail_in = n;
    istate.marker = m;
    if (m != 4) {
      return Z_DATA_ERROR2;
    }
    r = z.total_in;
    w = z.total_out;
    inflateReset(z);
    z.total_in = r;
    z.total_out = w;
    istate.mode = BLOCKS;
    return Z_OK2;
  };
  that.inflateSyncPoint = function(z) {
    if (!z || !z.istate || !z.istate.blocks)
      return Z_STREAM_ERROR2;
    return z.istate.blocks.sync_point();
  };
}
function ZStream2() {
}
ZStream2.prototype = {
  inflateInit(bits) {
    const that = this;
    that.istate = new Inflate();
    if (!bits)
      bits = MAX_BITS2;
    return that.istate.inflateInit(that, bits);
  },
  inflate(f) {
    const that = this;
    if (!that.istate)
      return Z_STREAM_ERROR2;
    return that.istate.inflate(that, f);
  },
  inflateEnd() {
    const that = this;
    if (!that.istate)
      return Z_STREAM_ERROR2;
    const ret = that.istate.inflateEnd(that);
    that.istate = null;
    return ret;
  },
  inflateSync() {
    const that = this;
    if (!that.istate)
      return Z_STREAM_ERROR2;
    return that.istate.inflateSync(that);
  },
  inflateSetDictionary(dictionary, dictLength) {
    const that = this;
    if (!that.istate)
      return Z_STREAM_ERROR2;
    return that.istate.inflateSetDictionary(that, dictionary, dictLength);
  },
  read_byte(start) {
    const that = this;
    return that.next_in[start];
  },
  read_buf(start, size) {
    const that = this;
    return that.next_in.subarray(start, start + size);
  }
};
function ZipInflate(options) {
  const that = this;
  const z = new ZStream2();
  const bufsize = options && options.chunkSize ? Math.floor(options.chunkSize * 2) : 128 * 1024;
  const flush = Z_NO_FLUSH2;
  const buf = new Uint8Array(bufsize);
  let nomoreinput = false;
  z.inflateInit();
  z.next_out = buf;
  that.append = function(data, onprogress) {
    const buffers = [];
    let err, array, lastIndex = 0, bufferIndex = 0, bufferSize = 0;
    if (data.length === 0)
      return;
    z.next_in_index = 0;
    z.next_in = data;
    z.avail_in = data.length;
    do {
      z.next_out_index = 0;
      z.avail_out = bufsize;
      if (z.avail_in === 0 && !nomoreinput) {
        z.next_in_index = 0;
        nomoreinput = true;
      }
      err = z.inflate(flush);
      if (nomoreinput && err === Z_BUF_ERROR2) {
        if (z.avail_in !== 0)
          throw new Error("inflating: bad input");
      } else if (err !== Z_OK2 && err !== Z_STREAM_END2)
        throw new Error("inflating: " + z.msg);
      if ((nomoreinput || err === Z_STREAM_END2) && z.avail_in === data.length)
        throw new Error("inflating: bad input");
      if (z.next_out_index)
        if (z.next_out_index === bufsize)
          buffers.push(new Uint8Array(buf));
        else
          buffers.push(buf.subarray(0, z.next_out_index));
      bufferSize += z.next_out_index;
      if (onprogress && z.next_in_index > 0 && z.next_in_index != lastIndex) {
        onprogress(z.next_in_index);
        lastIndex = z.next_in_index;
      }
    } while (z.avail_in > 0 || z.avail_out === 0);
    if (buffers.length > 1) {
      array = new Uint8Array(bufferSize);
      buffers.forEach(function(chunk) {
        array.set(chunk, bufferIndex);
        bufferIndex += chunk.length;
      });
    } else {
      array = buffers[0] ? new Uint8Array(buffers[0]) : new Uint8Array();
    }
    return array;
  };
  that.flush = function() {
    z.inflateEnd();
  };
}

// node_modules/@zip.js/zip.js/lib/core/constants.js
var MAX_32_BITS = 4294967295;
var MAX_16_BITS = 65535;
var COMPRESSION_METHOD_DEFLATE = 8;
var COMPRESSION_METHOD_STORE = 0;
var COMPRESSION_METHOD_AES = 99;
var LOCAL_FILE_HEADER_SIGNATURE = 67324752;
var SPLIT_ZIP_FILE_SIGNATURE = 134695760;
var CENTRAL_FILE_HEADER_SIGNATURE = 33639248;
var END_OF_CENTRAL_DIR_SIGNATURE = 101010256;
var ZIP64_END_OF_CENTRAL_DIR_SIGNATURE = 101075792;
var ZIP64_END_OF_CENTRAL_DIR_LOCATOR_SIGNATURE = 117853008;
var END_OF_CENTRAL_DIR_LENGTH = 22;
var ZIP64_END_OF_CENTRAL_DIR_LOCATOR_LENGTH = 20;
var ZIP64_END_OF_CENTRAL_DIR_LENGTH = 56;
var ZIP64_END_OF_CENTRAL_DIR_TOTAL_LENGTH = END_OF_CENTRAL_DIR_LENGTH + ZIP64_END_OF_CENTRAL_DIR_LOCATOR_LENGTH + ZIP64_END_OF_CENTRAL_DIR_LENGTH;
var EXTRAFIELD_TYPE_ZIP64 = 1;
var EXTRAFIELD_TYPE_AES = 39169;
var EXTRAFIELD_TYPE_NTFS = 10;
var EXTRAFIELD_TYPE_NTFS_TAG1 = 1;
var EXTRAFIELD_TYPE_EXTENDED_TIMESTAMP = 21589;
var EXTRAFIELD_TYPE_UNICODE_PATH = 28789;
var EXTRAFIELD_TYPE_UNICODE_COMMENT = 25461;
var EXTRAFIELD_TYPE_USDZ = 6534;
var BITFLAG_ENCRYPTED = 1;
var BITFLAG_LEVEL = 6;
var BITFLAG_DATA_DESCRIPTOR = 8;
var BITFLAG_LANG_ENCODING_FLAG = 2048;
var FILE_ATTR_MSDOS_DIR_MASK = 16;
var FILE_ATTR_UNIX_DIR_MASK = 16384;
var FILE_ATTR_UNIX_EXECUTABLE_MASK = 73;
var DIRECTORY_SIGNATURE = "/";
var MAX_DATE = new Date(2107, 11, 31);
var MIN_DATE = new Date(1980, 0, 1);
var UNDEFINED_VALUE = void 0;
var UNDEFINED_TYPE = "undefined";
var FUNCTION_TYPE = "function";

// node_modules/@zip.js/zip.js/lib/core/streams/stream-adapter.js
var StreamAdapter = class {
  constructor(Codec) {
    return class extends TransformStream {
      constructor(_format, options) {
        const codec2 = new Codec(options);
        super({
          transform(chunk, controller) {
            controller.enqueue(codec2.append(chunk));
          },
          flush(controller) {
            const chunk = codec2.flush();
            if (chunk) {
              controller.enqueue(chunk);
            }
          }
        });
      }
    };
  }
};

// node_modules/@zip.js/zip.js/lib/core/configuration.js
var MINIMUM_CHUNK_SIZE = 64;
var maxWorkers = 2;
try {
  if (typeof navigator != UNDEFINED_TYPE && navigator.hardwareConcurrency) {
    maxWorkers = navigator.hardwareConcurrency;
  }
} catch (_) {
}
var DEFAULT_CONFIGURATION = {
  chunkSize: 512 * 1024,
  maxWorkers,
  terminateWorkerTimeout: 5e3,
  useWebWorkers: true,
  useCompressionStream: true,
  workerScripts: UNDEFINED_VALUE,
  CompressionStreamNative: typeof CompressionStream != UNDEFINED_TYPE && CompressionStream,
  DecompressionStreamNative: typeof DecompressionStream != UNDEFINED_TYPE && DecompressionStream
};
var config = Object.assign({}, DEFAULT_CONFIGURATION);
function getConfiguration() {
  return config;
}
function getChunkSize(config2) {
  return Math.max(config2.chunkSize, MINIMUM_CHUNK_SIZE);
}
function configure(configuration) {
  const {
    baseURL: baseURL2,
    chunkSize,
    maxWorkers: maxWorkers2,
    terminateWorkerTimeout,
    useCompressionStream,
    useWebWorkers,
    Deflate: Deflate2,
    Inflate: Inflate2,
    CompressionStream: CompressionStream2,
    DecompressionStream: DecompressionStream2,
    workerScripts
  } = configuration;
  setIfDefined("baseURL", baseURL2);
  setIfDefined("chunkSize", chunkSize);
  setIfDefined("maxWorkers", maxWorkers2);
  setIfDefined("terminateWorkerTimeout", terminateWorkerTimeout);
  setIfDefined("useCompressionStream", useCompressionStream);
  setIfDefined("useWebWorkers", useWebWorkers);
  if (Deflate2) {
    config.CompressionStream = new StreamAdapter(Deflate2);
  }
  if (Inflate2) {
    config.DecompressionStream = new StreamAdapter(Inflate2);
  }
  setIfDefined("CompressionStream", CompressionStream2);
  setIfDefined("DecompressionStream", DecompressionStream2);
  if (workerScripts !== UNDEFINED_VALUE) {
    const { deflate, inflate } = workerScripts;
    if (deflate || inflate) {
      if (!config.workerScripts) {
        config.workerScripts = {};
      }
    }
    if (deflate) {
      if (!Array.isArray(deflate)) {
        throw new Error("workerScripts.deflate must be an array");
      }
      config.workerScripts.deflate = deflate;
    }
    if (inflate) {
      if (!Array.isArray(inflate)) {
        throw new Error("workerScripts.inflate must be an array");
      }
      config.workerScripts.inflate = inflate;
    }
  }
}
function setIfDefined(propertyName, propertyValue) {
  if (propertyValue !== UNDEFINED_VALUE) {
    config[propertyName] = propertyValue;
  }
}

// node_modules/@zip.js/zip.js/lib/core/util/mime-type.js
var table = {
  "application": {
    "andrew-inset": "ez",
    "annodex": "anx",
    "atom+xml": "atom",
    "atomcat+xml": "atomcat",
    "atomserv+xml": "atomsrv",
    "bbolin": "lin",
    "cu-seeme": "cu",
    "davmount+xml": "davmount",
    "dsptype": "tsp",
    "ecmascript": [
      "es",
      "ecma"
    ],
    "futuresplash": "spl",
    "hta": "hta",
    "java-archive": "jar",
    "java-serialized-object": "ser",
    "java-vm": "class",
    "m3g": "m3g",
    "mac-binhex40": "hqx",
    "mathematica": [
      "nb",
      "ma",
      "mb"
    ],
    "msaccess": "mdb",
    "msword": [
      "doc",
      "dot",
      "wiz"
    ],
    "mxf": "mxf",
    "oda": "oda",
    "ogg": "ogx",
    "pdf": "pdf",
    "pgp-keys": "key",
    "pgp-signature": [
      "asc",
      "sig"
    ],
    "pics-rules": "prf",
    "postscript": [
      "ps",
      "ai",
      "eps",
      "epsi",
      "epsf",
      "eps2",
      "eps3"
    ],
    "rar": "rar",
    "rdf+xml": "rdf",
    "rss+xml": "rss",
    "rtf": "rtf",
    "xhtml+xml": [
      "xhtml",
      "xht"
    ],
    "xml": [
      "xml",
      "xsl",
      "xsd",
      "xpdl"
    ],
    "xspf+xml": "xspf",
    "zip": "zip",
    "vnd.android.package-archive": "apk",
    "vnd.cinderella": "cdy",
    "vnd.google-earth.kml+xml": "kml",
    "vnd.google-earth.kmz": "kmz",
    "vnd.mozilla.xul+xml": "xul",
    "vnd.ms-excel": [
      "xls",
      "xlb",
      "xlt",
      "xlm",
      "xla",
      "xlc",
      "xlw"
    ],
    "vnd.ms-pki.seccat": "cat",
    "vnd.ms-pki.stl": "stl",
    "vnd.ms-powerpoint": [
      "ppt",
      "pps",
      "pot",
      "ppa",
      "pwz"
    ],
    "vnd.oasis.opendocument.chart": "odc",
    "vnd.oasis.opendocument.database": "odb",
    "vnd.oasis.opendocument.formula": "odf",
    "vnd.oasis.opendocument.graphics": "odg",
    "vnd.oasis.opendocument.graphics-template": "otg",
    "vnd.oasis.opendocument.image": "odi",
    "vnd.oasis.opendocument.presentation": "odp",
    "vnd.oasis.opendocument.presentation-template": "otp",
    "vnd.oasis.opendocument.spreadsheet": "ods",
    "vnd.oasis.opendocument.spreadsheet-template": "ots",
    "vnd.oasis.opendocument.text": "odt",
    "vnd.oasis.opendocument.text-master": [
      "odm",
      "otm"
    ],
    "vnd.oasis.opendocument.text-template": "ott",
    "vnd.oasis.opendocument.text-web": "oth",
    "vnd.openxmlformats-officedocument.spreadsheetml.sheet": "xlsx",
    "vnd.openxmlformats-officedocument.spreadsheetml.template": "xltx",
    "vnd.openxmlformats-officedocument.presentationml.presentation": "pptx",
    "vnd.openxmlformats-officedocument.presentationml.slideshow": "ppsx",
    "vnd.openxmlformats-officedocument.presentationml.template": "potx",
    "vnd.openxmlformats-officedocument.wordprocessingml.document": "docx",
    "vnd.openxmlformats-officedocument.wordprocessingml.template": "dotx",
    "vnd.smaf": "mmf",
    "vnd.stardivision.calc": "sdc",
    "vnd.stardivision.chart": "sds",
    "vnd.stardivision.draw": "sda",
    "vnd.stardivision.impress": "sdd",
    "vnd.stardivision.math": [
      "sdf",
      "smf"
    ],
    "vnd.stardivision.writer": [
      "sdw",
      "vor"
    ],
    "vnd.stardivision.writer-global": "sgl",
    "vnd.sun.xml.calc": "sxc",
    "vnd.sun.xml.calc.template": "stc",
    "vnd.sun.xml.draw": "sxd",
    "vnd.sun.xml.draw.template": "std",
    "vnd.sun.xml.impress": "sxi",
    "vnd.sun.xml.impress.template": "sti",
    "vnd.sun.xml.math": "sxm",
    "vnd.sun.xml.writer": "sxw",
    "vnd.sun.xml.writer.global": "sxg",
    "vnd.sun.xml.writer.template": "stw",
    "vnd.symbian.install": [
      "sis",
      "sisx"
    ],
    "vnd.visio": [
      "vsd",
      "vst",
      "vss",
      "vsw",
      "vsdx",
      "vssx",
      "vstx",
      "vssm",
      "vstm"
    ],
    "vnd.wap.wbxml": "wbxml",
    "vnd.wap.wmlc": "wmlc",
    "vnd.wap.wmlscriptc": "wmlsc",
    "vnd.wordperfect": "wpd",
    "vnd.wordperfect5.1": "wp5",
    "x-123": "wk",
    "x-7z-compressed": "7z",
    "x-abiword": "abw",
    "x-apple-diskimage": "dmg",
    "x-bcpio": "bcpio",
    "x-bittorrent": "torrent",
    "x-cbr": [
      "cbr",
      "cba",
      "cbt",
      "cb7"
    ],
    "x-cbz": "cbz",
    "x-cdf": [
      "cdf",
      "cda"
    ],
    "x-cdlink": "vcd",
    "x-chess-pgn": "pgn",
    "x-cpio": "cpio",
    "x-csh": "csh",
    "x-director": [
      "dir",
      "dxr",
      "cst",
      "cct",
      "cxt",
      "w3d",
      "fgd",
      "swa"
    ],
    "x-dms": "dms",
    "x-doom": "wad",
    "x-dvi": "dvi",
    "x-httpd-eruby": "rhtml",
    "x-font": "pcf.Z",
    "x-freemind": "mm",
    "x-gnumeric": "gnumeric",
    "x-go-sgf": "sgf",
    "x-graphing-calculator": "gcf",
    "x-gtar": [
      "gtar",
      "taz"
    ],
    "x-hdf": "hdf",
    "x-httpd-php": [
      "phtml",
      "pht",
      "php"
    ],
    "x-httpd-php-source": "phps",
    "x-httpd-php3": "php3",
    "x-httpd-php3-preprocessed": "php3p",
    "x-httpd-php4": "php4",
    "x-httpd-php5": "php5",
    "x-ica": "ica",
    "x-info": "info",
    "x-internet-signup": [
      "ins",
      "isp"
    ],
    "x-iphone": "iii",
    "x-iso9660-image": "iso",
    "x-java-jnlp-file": "jnlp",
    "x-jmol": "jmz",
    "x-killustrator": "kil",
    "x-latex": "latex",
    "x-lyx": "lyx",
    "x-lzx": "lzx",
    "x-maker": [
      "frm",
      "fb",
      "fbdoc"
    ],
    "x-ms-wmd": "wmd",
    "x-msdos-program": [
      "com",
      "exe",
      "bat",
      "dll"
    ],
    "x-netcdf": [
      "nc"
    ],
    "x-ns-proxy-autoconfig": [
      "pac",
      "dat"
    ],
    "x-nwc": "nwc",
    "x-object": "o",
    "x-oz-application": "oza",
    "x-pkcs7-certreqresp": "p7r",
    "x-python-code": [
      "pyc",
      "pyo"
    ],
    "x-qgis": [
      "qgs",
      "shp",
      "shx"
    ],
    "x-quicktimeplayer": "qtl",
    "x-redhat-package-manager": [
      "rpm",
      "rpa"
    ],
    "x-ruby": "rb",
    "x-sh": "sh",
    "x-shar": "shar",
    "x-shockwave-flash": [
      "swf",
      "swfl"
    ],
    "x-silverlight": "scr",
    "x-stuffit": "sit",
    "x-sv4cpio": "sv4cpio",
    "x-sv4crc": "sv4crc",
    "x-tar": "tar",
    "x-tex-gf": "gf",
    "x-tex-pk": "pk",
    "x-texinfo": [
      "texinfo",
      "texi"
    ],
    "x-trash": [
      "~",
      "%",
      "bak",
      "old",
      "sik"
    ],
    "x-ustar": "ustar",
    "x-wais-source": "src",
    "x-wingz": "wz",
    "x-x509-ca-cert": [
      "crt",
      "der",
      "cer"
    ],
    "x-xcf": "xcf",
    "x-xfig": "fig",
    "x-xpinstall": "xpi",
    "applixware": "aw",
    "atomsvc+xml": "atomsvc",
    "ccxml+xml": "ccxml",
    "cdmi-capability": "cdmia",
    "cdmi-container": "cdmic",
    "cdmi-domain": "cdmid",
    "cdmi-object": "cdmio",
    "cdmi-queue": "cdmiq",
    "docbook+xml": "dbk",
    "dssc+der": "dssc",
    "dssc+xml": "xdssc",
    "emma+xml": "emma",
    "epub+zip": "epub",
    "exi": "exi",
    "font-tdpfr": "pfr",
    "gml+xml": "gml",
    "gpx+xml": "gpx",
    "gxf": "gxf",
    "hyperstudio": "stk",
    "inkml+xml": [
      "ink",
      "inkml"
    ],
    "ipfix": "ipfix",
    "jsonml+json": "jsonml",
    "lost+xml": "lostxml",
    "mads+xml": "mads",
    "marc": "mrc",
    "marcxml+xml": "mrcx",
    "mathml+xml": [
      "mathml",
      "mml"
    ],
    "mbox": "mbox",
    "mediaservercontrol+xml": "mscml",
    "metalink+xml": "metalink",
    "metalink4+xml": "meta4",
    "mets+xml": "mets",
    "mods+xml": "mods",
    "mp21": [
      "m21",
      "mp21"
    ],
    "mp4": "mp4s",
    "oebps-package+xml": "opf",
    "omdoc+xml": "omdoc",
    "onenote": [
      "onetoc",
      "onetoc2",
      "onetmp",
      "onepkg"
    ],
    "oxps": "oxps",
    "patch-ops-error+xml": "xer",
    "pgp-encrypted": "pgp",
    "pkcs10": "p10",
    "pkcs7-mime": [
      "p7m",
      "p7c"
    ],
    "pkcs7-signature": "p7s",
    "pkcs8": "p8",
    "pkix-attr-cert": "ac",
    "pkix-crl": "crl",
    "pkix-pkipath": "pkipath",
    "pkixcmp": "pki",
    "pls+xml": "pls",
    "prs.cww": "cww",
    "pskc+xml": "pskcxml",
    "reginfo+xml": "rif",
    "relax-ng-compact-syntax": "rnc",
    "resource-lists+xml": "rl",
    "resource-lists-diff+xml": "rld",
    "rls-services+xml": "rs",
    "rpki-ghostbusters": "gbr",
    "rpki-manifest": "mft",
    "rpki-roa": "roa",
    "rsd+xml": "rsd",
    "sbml+xml": "sbml",
    "scvp-cv-request": "scq",
    "scvp-cv-response": "scs",
    "scvp-vp-request": "spq",
    "scvp-vp-response": "spp",
    "sdp": "sdp",
    "set-payment-initiation": "setpay",
    "set-registration-initiation": "setreg",
    "shf+xml": "shf",
    "sparql-query": "rq",
    "sparql-results+xml": "srx",
    "srgs": "gram",
    "srgs+xml": "grxml",
    "sru+xml": "sru",
    "ssdl+xml": "ssdl",
    "ssml+xml": "ssml",
    "tei+xml": [
      "tei",
      "teicorpus"
    ],
    "thraud+xml": "tfi",
    "timestamped-data": "tsd",
    "vnd.3gpp.pic-bw-large": "plb",
    "vnd.3gpp.pic-bw-small": "psb",
    "vnd.3gpp.pic-bw-var": "pvb",
    "vnd.3gpp2.tcap": "tcap",
    "vnd.3m.post-it-notes": "pwn",
    "vnd.accpac.simply.aso": "aso",
    "vnd.accpac.simply.imp": "imp",
    "vnd.acucobol": "acu",
    "vnd.acucorp": [
      "atc",
      "acutc"
    ],
    "vnd.adobe.air-application-installer-package+zip": "air",
    "vnd.adobe.formscentral.fcdt": "fcdt",
    "vnd.adobe.fxp": [
      "fxp",
      "fxpl"
    ],
    "vnd.adobe.xdp+xml": "xdp",
    "vnd.adobe.xfdf": "xfdf",
    "vnd.ahead.space": "ahead",
    "vnd.airzip.filesecure.azf": "azf",
    "vnd.airzip.filesecure.azs": "azs",
    "vnd.amazon.ebook": "azw",
    "vnd.americandynamics.acc": "acc",
    "vnd.amiga.ami": "ami",
    "vnd.anser-web-certificate-issue-initiation": "cii",
    "vnd.anser-web-funds-transfer-initiation": "fti",
    "vnd.antix.game-component": "atx",
    "vnd.apple.installer+xml": "mpkg",
    "vnd.apple.mpegurl": "m3u8",
    "vnd.aristanetworks.swi": "swi",
    "vnd.astraea-software.iota": "iota",
    "vnd.audiograph": "aep",
    "vnd.blueice.multipass": "mpm",
    "vnd.bmi": "bmi",
    "vnd.businessobjects": "rep",
    "vnd.chemdraw+xml": "cdxml",
    "vnd.chipnuts.karaoke-mmd": "mmd",
    "vnd.claymore": "cla",
    "vnd.cloanto.rp9": "rp9",
    "vnd.clonk.c4group": [
      "c4g",
      "c4d",
      "c4f",
      "c4p",
      "c4u"
    ],
    "vnd.cluetrust.cartomobile-config": "c11amc",
    "vnd.cluetrust.cartomobile-config-pkg": "c11amz",
    "vnd.commonspace": "csp",
    "vnd.contact.cmsg": "cdbcmsg",
    "vnd.cosmocaller": "cmc",
    "vnd.crick.clicker": "clkx",
    "vnd.crick.clicker.keyboard": "clkk",
    "vnd.crick.clicker.palette": "clkp",
    "vnd.crick.clicker.template": "clkt",
    "vnd.crick.clicker.wordbank": "clkw",
    "vnd.criticaltools.wbs+xml": "wbs",
    "vnd.ctc-posml": "pml",
    "vnd.cups-ppd": "ppd",
    "vnd.curl.car": "car",
    "vnd.curl.pcurl": "pcurl",
    "vnd.dart": "dart",
    "vnd.data-vision.rdz": "rdz",
    "vnd.dece.data": [
      "uvf",
      "uvvf",
      "uvd",
      "uvvd"
    ],
    "vnd.dece.ttml+xml": [
      "uvt",
      "uvvt"
    ],
    "vnd.dece.unspecified": [
      "uvx",
      "uvvx"
    ],
    "vnd.dece.zip": [
      "uvz",
      "uvvz"
    ],
    "vnd.denovo.fcselayout-link": "fe_launch",
    "vnd.dna": "dna",
    "vnd.dolby.mlp": "mlp",
    "vnd.dpgraph": "dpg",
    "vnd.dreamfactory": "dfac",
    "vnd.ds-keypoint": "kpxx",
    "vnd.dvb.ait": "ait",
    "vnd.dvb.service": "svc",
    "vnd.dynageo": "geo",
    "vnd.ecowin.chart": "mag",
    "vnd.enliven": "nml",
    "vnd.epson.esf": "esf",
    "vnd.epson.msf": "msf",
    "vnd.epson.quickanime": "qam",
    "vnd.epson.salt": "slt",
    "vnd.epson.ssf": "ssf",
    "vnd.eszigno3+xml": [
      "es3",
      "et3"
    ],
    "vnd.ezpix-album": "ez2",
    "vnd.ezpix-package": "ez3",
    "vnd.fdf": "fdf",
    "vnd.fdsn.mseed": "mseed",
    "vnd.fdsn.seed": [
      "seed",
      "dataless"
    ],
    "vnd.flographit": "gph",
    "vnd.fluxtime.clip": "ftc",
    "vnd.framemaker": [
      "fm",
      "frame",
      "maker",
      "book"
    ],
    "vnd.frogans.fnc": "fnc",
    "vnd.frogans.ltf": "ltf",
    "vnd.fsc.weblaunch": "fsc",
    "vnd.fujitsu.oasys": "oas",
    "vnd.fujitsu.oasys2": "oa2",
    "vnd.fujitsu.oasys3": "oa3",
    "vnd.fujitsu.oasysgp": "fg5",
    "vnd.fujitsu.oasysprs": "bh2",
    "vnd.fujixerox.ddd": "ddd",
    "vnd.fujixerox.docuworks": "xdw",
    "vnd.fujixerox.docuworks.binder": "xbd",
    "vnd.fuzzysheet": "fzs",
    "vnd.genomatix.tuxedo": "txd",
    "vnd.geogebra.file": "ggb",
    "vnd.geogebra.tool": "ggt",
    "vnd.geometry-explorer": [
      "gex",
      "gre"
    ],
    "vnd.geonext": "gxt",
    "vnd.geoplan": "g2w",
    "vnd.geospace": "g3w",
    "vnd.gmx": "gmx",
    "vnd.grafeq": [
      "gqf",
      "gqs"
    ],
    "vnd.groove-account": "gac",
    "vnd.groove-help": "ghf",
    "vnd.groove-identity-message": "gim",
    "vnd.groove-injector": "grv",
    "vnd.groove-tool-message": "gtm",
    "vnd.groove-tool-template": "tpl",
    "vnd.groove-vcard": "vcg",
    "vnd.hal+xml": "hal",
    "vnd.handheld-entertainment+xml": "zmm",
    "vnd.hbci": "hbci",
    "vnd.hhe.lesson-player": "les",
    "vnd.hp-hpgl": "hpgl",
    "vnd.hp-hpid": "hpid",
    "vnd.hp-hps": "hps",
    "vnd.hp-jlyt": "jlt",
    "vnd.hp-pcl": "pcl",
    "vnd.hp-pclxl": "pclxl",
    "vnd.hydrostatix.sof-data": "sfd-hdstx",
    "vnd.ibm.minipay": "mpy",
    "vnd.ibm.modcap": [
      "afp",
      "listafp",
      "list3820"
    ],
    "vnd.ibm.rights-management": "irm",
    "vnd.ibm.secure-container": "sc",
    "vnd.iccprofile": [
      "icc",
      "icm"
    ],
    "vnd.igloader": "igl",
    "vnd.immervision-ivp": "ivp",
    "vnd.immervision-ivu": "ivu",
    "vnd.insors.igm": "igm",
    "vnd.intercon.formnet": [
      "xpw",
      "xpx"
    ],
    "vnd.intergeo": "i2g",
    "vnd.intu.qbo": "qbo",
    "vnd.intu.qfx": "qfx",
    "vnd.ipunplugged.rcprofile": "rcprofile",
    "vnd.irepository.package+xml": "irp",
    "vnd.is-xpr": "xpr",
    "vnd.isac.fcs": "fcs",
    "vnd.jam": "jam",
    "vnd.jcp.javame.midlet-rms": "rms",
    "vnd.jisp": "jisp",
    "vnd.joost.joda-archive": "joda",
    "vnd.kahootz": [
      "ktz",
      "ktr"
    ],
    "vnd.kde.karbon": "karbon",
    "vnd.kde.kchart": "chrt",
    "vnd.kde.kformula": "kfo",
    "vnd.kde.kivio": "flw",
    "vnd.kde.kontour": "kon",
    "vnd.kde.kpresenter": [
      "kpr",
      "kpt"
    ],
    "vnd.kde.kspread": "ksp",
    "vnd.kde.kword": [
      "kwd",
      "kwt"
    ],
    "vnd.kenameaapp": "htke",
    "vnd.kidspiration": "kia",
    "vnd.kinar": [
      "kne",
      "knp"
    ],
    "vnd.koan": [
      "skp",
      "skd",
      "skt",
      "skm"
    ],
    "vnd.kodak-descriptor": "sse",
    "vnd.las.las+xml": "lasxml",
    "vnd.llamagraphics.life-balance.desktop": "lbd",
    "vnd.llamagraphics.life-balance.exchange+xml": "lbe",
    "vnd.lotus-1-2-3": "123",
    "vnd.lotus-approach": "apr",
    "vnd.lotus-freelance": "pre",
    "vnd.lotus-notes": "nsf",
    "vnd.lotus-organizer": "org",
    "vnd.lotus-screencam": "scm",
    "vnd.lotus-wordpro": "lwp",
    "vnd.macports.portpkg": "portpkg",
    "vnd.mcd": "mcd",
    "vnd.medcalcdata": "mc1",
    "vnd.mediastation.cdkey": "cdkey",
    "vnd.mfer": "mwf",
    "vnd.mfmp": "mfm",
    "vnd.micrografx.flo": "flo",
    "vnd.micrografx.igx": "igx",
    "vnd.mif": "mif",
    "vnd.mobius.daf": "daf",
    "vnd.mobius.dis": "dis",
    "vnd.mobius.mbk": "mbk",
    "vnd.mobius.mqy": "mqy",
    "vnd.mobius.msl": "msl",
    "vnd.mobius.plc": "plc",
    "vnd.mobius.txf": "txf",
    "vnd.mophun.application": "mpn",
    "vnd.mophun.certificate": "mpc",
    "vnd.ms-artgalry": "cil",
    "vnd.ms-cab-compressed": "cab",
    "vnd.ms-excel.addin.macroenabled.12": "xlam",
    "vnd.ms-excel.sheet.binary.macroenabled.12": "xlsb",
    "vnd.ms-excel.sheet.macroenabled.12": "xlsm",
    "vnd.ms-excel.template.macroenabled.12": "xltm",
    "vnd.ms-fontobject": "eot",
    "vnd.ms-htmlhelp": "chm",
    "vnd.ms-ims": "ims",
    "vnd.ms-lrm": "lrm",
    "vnd.ms-officetheme": "thmx",
    "vnd.ms-powerpoint.addin.macroenabled.12": "ppam",
    "vnd.ms-powerpoint.presentation.macroenabled.12": "pptm",
    "vnd.ms-powerpoint.slide.macroenabled.12": "sldm",
    "vnd.ms-powerpoint.slideshow.macroenabled.12": "ppsm",
    "vnd.ms-powerpoint.template.macroenabled.12": "potm",
    "vnd.ms-project": [
      "mpp",
      "mpt"
    ],
    "vnd.ms-word.document.macroenabled.12": "docm",
    "vnd.ms-word.template.macroenabled.12": "dotm",
    "vnd.ms-works": [
      "wps",
      "wks",
      "wcm",
      "wdb"
    ],
    "vnd.ms-wpl": "wpl",
    "vnd.ms-xpsdocument": "xps",
    "vnd.mseq": "mseq",
    "vnd.musician": "mus",
    "vnd.muvee.style": "msty",
    "vnd.mynfc": "taglet",
    "vnd.neurolanguage.nlu": "nlu",
    "vnd.nitf": [
      "ntf",
      "nitf"
    ],
    "vnd.noblenet-directory": "nnd",
    "vnd.noblenet-sealer": "nns",
    "vnd.noblenet-web": "nnw",
    "vnd.nokia.n-gage.data": "ngdat",
    "vnd.nokia.n-gage.symbian.install": "n-gage",
    "vnd.nokia.radio-preset": "rpst",
    "vnd.nokia.radio-presets": "rpss",
    "vnd.novadigm.edm": "edm",
    "vnd.novadigm.edx": "edx",
    "vnd.novadigm.ext": "ext",
    "vnd.oasis.opendocument.chart-template": "otc",
    "vnd.oasis.opendocument.formula-template": "odft",
    "vnd.oasis.opendocument.image-template": "oti",
    "vnd.olpc-sugar": "xo",
    "vnd.oma.dd2+xml": "dd2",
    "vnd.openofficeorg.extension": "oxt",
    "vnd.openxmlformats-officedocument.presentationml.slide": "sldx",
    "vnd.osgeo.mapguide.package": "mgp",
    "vnd.osgi.dp": "dp",
    "vnd.osgi.subsystem": "esa",
    "vnd.palm": [
      "pdb",
      "pqa",
      "oprc"
    ],
    "vnd.pawaafile": "paw",
    "vnd.pg.format": "str",
    "vnd.pg.osasli": "ei6",
    "vnd.picsel": "efif",
    "vnd.pmi.widget": "wg",
    "vnd.pocketlearn": "plf",
    "vnd.powerbuilder6": "pbd",
    "vnd.previewsystems.box": "box",
    "vnd.proteus.magazine": "mgz",
    "vnd.publishare-delta-tree": "qps",
    "vnd.pvi.ptid1": "ptid",
    "vnd.quark.quarkxpress": [
      "qxd",
      "qxt",
      "qwd",
      "qwt",
      "qxl",
      "qxb"
    ],
    "vnd.realvnc.bed": "bed",
    "vnd.recordare.musicxml": "mxl",
    "vnd.recordare.musicxml+xml": "musicxml",
    "vnd.rig.cryptonote": "cryptonote",
    "vnd.rn-realmedia": "rm",
    "vnd.rn-realmedia-vbr": "rmvb",
    "vnd.route66.link66+xml": "link66",
    "vnd.sailingtracker.track": "st",
    "vnd.seemail": "see",
    "vnd.sema": "sema",
    "vnd.semd": "semd",
    "vnd.semf": "semf",
    "vnd.shana.informed.formdata": "ifm",
    "vnd.shana.informed.formtemplate": "itp",
    "vnd.shana.informed.interchange": "iif",
    "vnd.shana.informed.package": "ipk",
    "vnd.simtech-mindmapper": [
      "twd",
      "twds"
    ],
    "vnd.smart.teacher": "teacher",
    "vnd.solent.sdkm+xml": [
      "sdkm",
      "sdkd"
    ],
    "vnd.spotfire.dxp": "dxp",
    "vnd.spotfire.sfs": "sfs",
    "vnd.stepmania.package": "smzip",
    "vnd.stepmania.stepchart": "sm",
    "vnd.sus-calendar": [
      "sus",
      "susp"
    ],
    "vnd.svd": "svd",
    "vnd.syncml+xml": "xsm",
    "vnd.syncml.dm+wbxml": "bdm",
    "vnd.syncml.dm+xml": "xdm",
    "vnd.tao.intent-module-archive": "tao",
    "vnd.tcpdump.pcap": [
      "pcap",
      "cap",
      "dmp"
    ],
    "vnd.tmobile-livetv": "tmo",
    "vnd.trid.tpt": "tpt",
    "vnd.triscape.mxs": "mxs",
    "vnd.trueapp": "tra",
    "vnd.ufdl": [
      "ufd",
      "ufdl"
    ],
    "vnd.uiq.theme": "utz",
    "vnd.umajin": "umj",
    "vnd.unity": "unityweb",
    "vnd.uoml+xml": "uoml",
    "vnd.vcx": "vcx",
    "vnd.visionary": "vis",
    "vnd.vsf": "vsf",
    "vnd.webturbo": "wtb",
    "vnd.wolfram.player": "nbp",
    "vnd.wqd": "wqd",
    "vnd.wt.stf": "stf",
    "vnd.xara": "xar",
    "vnd.xfdl": "xfdl",
    "vnd.yamaha.hv-dic": "hvd",
    "vnd.yamaha.hv-script": "hvs",
    "vnd.yamaha.hv-voice": "hvp",
    "vnd.yamaha.openscoreformat": "osf",
    "vnd.yamaha.openscoreformat.osfpvg+xml": "osfpvg",
    "vnd.yamaha.smaf-audio": "saf",
    "vnd.yamaha.smaf-phrase": "spf",
    "vnd.yellowriver-custom-menu": "cmp",
    "vnd.zul": [
      "zir",
      "zirz"
    ],
    "vnd.zzazz.deck+xml": "zaz",
    "voicexml+xml": "vxml",
    "widget": "wgt",
    "winhlp": "hlp",
    "wsdl+xml": "wsdl",
    "wspolicy+xml": "wspolicy",
    "x-ace-compressed": "ace",
    "x-authorware-bin": [
      "aab",
      "x32",
      "u32",
      "vox"
    ],
    "x-authorware-map": "aam",
    "x-authorware-seg": "aas",
    "x-blorb": [
      "blb",
      "blorb"
    ],
    "x-bzip": "bz",
    "x-bzip2": [
      "bz2",
      "boz"
    ],
    "x-cfs-compressed": "cfs",
    "x-chat": "chat",
    "x-conference": "nsc",
    "x-dgc-compressed": "dgc",
    "x-dtbncx+xml": "ncx",
    "x-dtbook+xml": "dtb",
    "x-dtbresource+xml": "res",
    "x-eva": "eva",
    "x-font-bdf": "bdf",
    "x-font-ghostscript": "gsf",
    "x-font-linux-psf": "psf",
    "x-font-pcf": "pcf",
    "x-font-snf": "snf",
    "x-font-ttf": [
      "ttf",
      "ttc"
    ],
    "x-font-type1": [
      "pfa",
      "pfb",
      "pfm",
      "afm"
    ],
    "x-freearc": "arc",
    "x-gca-compressed": "gca",
    "x-glulx": "ulx",
    "x-gramps-xml": "gramps",
    "x-install-instructions": "install",
    "x-lzh-compressed": [
      "lzh",
      "lha"
    ],
    "x-mie": "mie",
    "x-mobipocket-ebook": [
      "prc",
      "mobi"
    ],
    "x-ms-application": "application",
    "x-ms-shortcut": "lnk",
    "x-ms-xbap": "xbap",
    "x-msbinder": "obd",
    "x-mscardfile": "crd",
    "x-msclip": "clp",
    "application/x-ms-installer": "msi",
    "x-msmediaview": [
      "mvb",
      "m13",
      "m14"
    ],
    "x-msmetafile": [
      "wmf",
      "wmz",
      "emf",
      "emz"
    ],
    "x-msmoney": "mny",
    "x-mspublisher": "pub",
    "x-msschedule": "scd",
    "x-msterminal": "trm",
    "x-mswrite": "wri",
    "x-nzb": "nzb",
    "x-pkcs12": [
      "p12",
      "pfx"
    ],
    "x-pkcs7-certificates": [
      "p7b",
      "spc"
    ],
    "x-research-info-systems": "ris",
    "x-silverlight-app": "xap",
    "x-sql": "sql",
    "x-stuffitx": "sitx",
    "x-subrip": "srt",
    "x-t3vm-image": "t3",
    "x-tex-tfm": "tfm",
    "x-tgif": "obj",
    "x-xliff+xml": "xlf",
    "x-xz": "xz",
    "x-zmachine": [
      "z1",
      "z2",
      "z3",
      "z4",
      "z5",
      "z6",
      "z7",
      "z8"
    ],
    "xaml+xml": "xaml",
    "xcap-diff+xml": "xdf",
    "xenc+xml": "xenc",
    "xml-dtd": "dtd",
    "xop+xml": "xop",
    "xproc+xml": "xpl",
    "xslt+xml": "xslt",
    "xv+xml": [
      "mxml",
      "xhvml",
      "xvml",
      "xvm"
    ],
    "yang": "yang",
    "yin+xml": "yin",
    "envoy": "evy",
    "fractals": "fif",
    "internet-property-stream": "acx",
    "olescript": "axs",
    "vnd.ms-outlook": "msg",
    "vnd.ms-pkicertstore": "sst",
    "x-compress": "z",
    "x-perfmon": [
      "pma",
      "pmc",
      "pmr",
      "pmw"
    ],
    "ynd.ms-pkipko": "pko",
    "gzip": [
      "gz",
      "tgz"
    ],
    "smil+xml": [
      "smi",
      "smil"
    ],
    "vnd.debian.binary-package": [
      "deb",
      "udeb"
    ],
    "vnd.hzn-3d-crossword": "x3d",
    "vnd.sqlite3": [
      "db",
      "sqlite",
      "sqlite3",
      "db-wal",
      "sqlite-wal",
      "db-shm",
      "sqlite-shm"
    ],
    "vnd.wap.sic": "sic",
    "vnd.wap.slc": "slc",
    "x-krita": [
      "kra",
      "krz"
    ],
    "x-perl": [
      "pm",
      "pl"
    ],
    "yaml": [
      "yaml",
      "yml"
    ]
  },
  "audio": {
    "amr": "amr",
    "amr-wb": "awb",
    "annodex": "axa",
    "basic": [
      "au",
      "snd"
    ],
    "flac": "flac",
    "midi": [
      "mid",
      "midi",
      "kar",
      "rmi"
    ],
    "mpeg": [
      "mpga",
      "mpega",
      "mp3",
      "m4a",
      "mp2a",
      "m2a",
      "m3a"
    ],
    "mpegurl": "m3u",
    "ogg": [
      "oga",
      "ogg",
      "spx"
    ],
    "prs.sid": "sid",
    "x-aiff": "aifc",
    "x-gsm": "gsm",
    "x-ms-wma": "wma",
    "x-ms-wax": "wax",
    "x-pn-realaudio": "ram",
    "x-realaudio": "ra",
    "x-sd2": "sd2",
    "adpcm": "adp",
    "mp4": "mp4a",
    "s3m": "s3m",
    "silk": "sil",
    "vnd.dece.audio": [
      "uva",
      "uvva"
    ],
    "vnd.digital-winds": "eol",
    "vnd.dra": "dra",
    "vnd.dts": "dts",
    "vnd.dts.hd": "dtshd",
    "vnd.lucent.voice": "lvp",
    "vnd.ms-playready.media.pya": "pya",
    "vnd.nuera.ecelp4800": "ecelp4800",
    "vnd.nuera.ecelp7470": "ecelp7470",
    "vnd.nuera.ecelp9600": "ecelp9600",
    "vnd.rip": "rip",
    "webm": "weba",
    "x-caf": "caf",
    "x-matroska": "mka",
    "x-pn-realaudio-plugin": "rmp",
    "xm": "xm",
    "aac": "aac",
    "aiff": [
      "aiff",
      "aif",
      "aff"
    ],
    "opus": "opus",
    "wav": "wav"
  },
  "chemical": {
    "x-alchemy": "alc",
    "x-cache": [
      "cac",
      "cache"
    ],
    "x-cache-csf": "csf",
    "x-cactvs-binary": [
      "cbin",
      "cascii",
      "ctab"
    ],
    "x-cdx": "cdx",
    "x-chem3d": "c3d",
    "x-cif": "cif",
    "x-cmdf": "cmdf",
    "x-cml": "cml",
    "x-compass": "cpa",
    "x-crossfire": "bsd",
    "x-csml": [
      "csml",
      "csm"
    ],
    "x-ctx": "ctx",
    "x-cxf": [
      "cxf",
      "cef"
    ],
    "x-embl-dl-nucleotide": [
      "emb",
      "embl"
    ],
    "x-gamess-input": [
      "inp",
      "gam",
      "gamin"
    ],
    "x-gaussian-checkpoint": [
      "fch",
      "fchk"
    ],
    "x-gaussian-cube": "cub",
    "x-gaussian-input": [
      "gau",
      "gjc",
      "gjf"
    ],
    "x-gaussian-log": "gal",
    "x-gcg8-sequence": "gcg",
    "x-genbank": "gen",
    "x-hin": "hin",
    "x-isostar": [
      "istr",
      "ist"
    ],
    "x-jcamp-dx": [
      "jdx",
      "dx"
    ],
    "x-kinemage": "kin",
    "x-macmolecule": "mcm",
    "x-macromodel-input": "mmod",
    "x-mdl-molfile": "mol",
    "x-mdl-rdfile": "rd",
    "x-mdl-rxnfile": "rxn",
    "x-mdl-sdfile": "sd",
    "x-mdl-tgf": "tgf",
    "x-mmcif": "mcif",
    "x-mol2": "mol2",
    "x-molconn-Z": "b",
    "x-mopac-graph": "gpt",
    "x-mopac-input": [
      "mop",
      "mopcrt",
      "zmt"
    ],
    "x-mopac-out": "moo",
    "x-ncbi-asn1": "asn",
    "x-ncbi-asn1-ascii": [
      "prt",
      "ent"
    ],
    "x-ncbi-asn1-binary": "val",
    "x-rosdal": "ros",
    "x-swissprot": "sw",
    "x-vamas-iso14976": "vms",
    "x-vmd": "vmd",
    "x-xtel": "xtel",
    "x-xyz": "xyz"
  },
  "font": {
    "otf": "otf",
    "woff": "woff",
    "woff2": "woff2"
  },
  "image": {
    "gif": "gif",
    "ief": "ief",
    "jpeg": [
      "jpeg",
      "jpg",
      "jpe",
      "jfif",
      "jfif-tbnl",
      "jif"
    ],
    "pcx": "pcx",
    "png": "png",
    "svg+xml": [
      "svg",
      "svgz"
    ],
    "tiff": [
      "tiff",
      "tif"
    ],
    "vnd.djvu": [
      "djvu",
      "djv"
    ],
    "vnd.wap.wbmp": "wbmp",
    "x-canon-cr2": "cr2",
    "x-canon-crw": "crw",
    "x-cmu-raster": "ras",
    "x-coreldraw": "cdr",
    "x-coreldrawpattern": "pat",
    "x-coreldrawtemplate": "cdt",
    "x-corelphotopaint": "cpt",
    "x-epson-erf": "erf",
    "x-icon": "ico",
    "x-jg": "art",
    "x-jng": "jng",
    "x-nikon-nef": "nef",
    "x-olympus-orf": "orf",
    "x-portable-anymap": "pnm",
    "x-portable-bitmap": "pbm",
    "x-portable-graymap": "pgm",
    "x-portable-pixmap": "ppm",
    "x-rgb": "rgb",
    "x-xbitmap": "xbm",
    "x-xpixmap": "xpm",
    "x-xwindowdump": "xwd",
    "bmp": "bmp",
    "cgm": "cgm",
    "g3fax": "g3",
    "ktx": "ktx",
    "prs.btif": "btif",
    "sgi": "sgi",
    "vnd.dece.graphic": [
      "uvi",
      "uvvi",
      "uvg",
      "uvvg"
    ],
    "vnd.dwg": "dwg",
    "vnd.dxf": "dxf",
    "vnd.fastbidsheet": "fbs",
    "vnd.fpx": "fpx",
    "vnd.fst": "fst",
    "vnd.fujixerox.edmics-mmr": "mmr",
    "vnd.fujixerox.edmics-rlc": "rlc",
    "vnd.ms-modi": "mdi",
    "vnd.ms-photo": "wdp",
    "vnd.net-fpx": "npx",
    "vnd.xiff": "xif",
    "webp": "webp",
    "x-3ds": "3ds",
    "x-cmx": "cmx",
    "x-freehand": [
      "fh",
      "fhc",
      "fh4",
      "fh5",
      "fh7"
    ],
    "x-pict": [
      "pic",
      "pct"
    ],
    "x-tga": "tga",
    "cis-cod": "cod",
    "avif": "avifs",
    "heic": [
      "heif",
      "heic"
    ],
    "pjpeg": [
      "pjpg"
    ],
    "vnd.adobe.photoshop": "psd",
    "x-adobe-dng": "dng",
    "x-fuji-raf": "raf",
    "x-icns": "icns",
    "x-kodak-dcr": "dcr",
    "x-kodak-k25": "k25",
    "x-kodak-kdc": "kdc",
    "x-minolta-mrw": "mrw",
    "x-panasonic-raw": [
      "raw",
      "rw2",
      "rwl"
    ],
    "x-pentax-pef": [
      "pef",
      "ptx"
    ],
    "x-sigma-x3f": "x3f",
    "x-sony-arw": "arw",
    "x-sony-sr2": "sr2",
    "x-sony-srf": "srf"
  },
  "message": {
    "rfc822": [
      "eml",
      "mime",
      "mht",
      "mhtml",
      "nws"
    ]
  },
  "model": {
    "iges": [
      "igs",
      "iges"
    ],
    "mesh": [
      "msh",
      "mesh",
      "silo"
    ],
    "vrml": [
      "wrl",
      "vrml"
    ],
    "x3d+vrml": [
      "x3dv",
      "x3dvz"
    ],
    "x3d+xml": "x3dz",
    "x3d+binary": [
      "x3db",
      "x3dbz"
    ],
    "vnd.collada+xml": "dae",
    "vnd.dwf": "dwf",
    "vnd.gdl": "gdl",
    "vnd.gtw": "gtw",
    "vnd.mts": "mts",
    "vnd.usdz+zip": "usdz",
    "vnd.vtu": "vtu"
  },
  "text": {
    "cache-manifest": [
      "manifest",
      "appcache"
    ],
    "calendar": [
      "ics",
      "icz",
      "ifb"
    ],
    "css": "css",
    "csv": "csv",
    "h323": "323",
    "html": [
      "html",
      "htm",
      "shtml",
      "stm"
    ],
    "iuls": "uls",
    "plain": [
      "txt",
      "text",
      "brf",
      "conf",
      "def",
      "list",
      "log",
      "in",
      "bas",
      "diff",
      "ksh"
    ],
    "richtext": "rtx",
    "scriptlet": [
      "sct",
      "wsc"
    ],
    "texmacs": "tm",
    "tab-separated-values": "tsv",
    "vnd.sun.j2me.app-descriptor": "jad",
    "vnd.wap.wml": "wml",
    "vnd.wap.wmlscript": "wmls",
    "x-bibtex": "bib",
    "x-boo": "boo",
    "x-c++hdr": [
      "h++",
      "hpp",
      "hxx",
      "hh"
    ],
    "x-c++src": [
      "c++",
      "cpp",
      "cxx",
      "cc"
    ],
    "x-component": "htc",
    "x-dsrc": "d",
    "x-diff": "patch",
    "x-haskell": "hs",
    "x-java": "java",
    "x-literate-haskell": "lhs",
    "x-moc": "moc",
    "x-pascal": [
      "p",
      "pas",
      "pp",
      "inc"
    ],
    "x-pcs-gcd": "gcd",
    "x-python": "py",
    "x-scala": "scala",
    "x-setext": "etx",
    "x-tcl": [
      "tcl",
      "tk"
    ],
    "x-tex": [
      "tex",
      "ltx",
      "sty",
      "cls"
    ],
    "x-vcalendar": "vcs",
    "x-vcard": "vcf",
    "n3": "n3",
    "prs.lines.tag": "dsc",
    "sgml": [
      "sgml",
      "sgm"
    ],
    "troff": [
      "t",
      "tr",
      "roff",
      "man",
      "me",
      "ms"
    ],
    "turtle": "ttl",
    "uri-list": [
      "uri",
      "uris",
      "urls"
    ],
    "vcard": "vcard",
    "vnd.curl": "curl",
    "vnd.curl.dcurl": "dcurl",
    "vnd.curl.scurl": "scurl",
    "vnd.curl.mcurl": "mcurl",
    "vnd.dvb.subtitle": "sub",
    "vnd.fly": "fly",
    "vnd.fmi.flexstor": "flx",
    "vnd.graphviz": "gv",
    "vnd.in3d.3dml": "3dml",
    "vnd.in3d.spot": "spot",
    "x-asm": [
      "s",
      "asm"
    ],
    "x-c": [
      "c",
      "h",
      "dic"
    ],
    "x-fortran": [
      "f",
      "for",
      "f77",
      "f90"
    ],
    "x-opml": "opml",
    "x-nfo": "nfo",
    "x-sfv": "sfv",
    "x-uuencode": "uu",
    "webviewhtml": "htt",
    "javascript": "js",
    "json": "json",
    "markdown": [
      "md",
      "markdown",
      "mdown",
      "markdn"
    ],
    "vnd.wap.si": "si",
    "vnd.wap.sl": "sl"
  },
  "video": {
    "avif": "avif",
    "3gpp": "3gp",
    "annodex": "axv",
    "dl": "dl",
    "dv": [
      "dif",
      "dv"
    ],
    "fli": "fli",
    "gl": "gl",
    "mpeg": [
      "mpeg",
      "mpg",
      "mpe",
      "m1v",
      "m2v",
      "mp2",
      "mpa",
      "mpv2"
    ],
    "mp4": [
      "mp4",
      "mp4v",
      "mpg4"
    ],
    "quicktime": [
      "qt",
      "mov"
    ],
    "ogg": "ogv",
    "vnd.mpegurl": [
      "mxu",
      "m4u"
    ],
    "x-flv": "flv",
    "x-la-asf": [
      "lsf",
      "lsx"
    ],
    "x-mng": "mng",
    "x-ms-asf": [
      "asf",
      "asx",
      "asr"
    ],
    "x-ms-wm": "wm",
    "x-ms-wmv": "wmv",
    "x-ms-wmx": "wmx",
    "x-ms-wvx": "wvx",
    "x-msvideo": "avi",
    "x-sgi-movie": "movie",
    "x-matroska": [
      "mpv",
      "mkv",
      "mk3d",
      "mks"
    ],
    "3gpp2": "3g2",
    "h261": "h261",
    "h263": "h263",
    "h264": "h264",
    "jpeg": "jpgv",
    "jpm": [
      "jpm",
      "jpgm"
    ],
    "mj2": [
      "mj2",
      "mjp2"
    ],
    "vnd.dece.hd": [
      "uvh",
      "uvvh"
    ],
    "vnd.dece.mobile": [
      "uvm",
      "uvvm"
    ],
    "vnd.dece.pd": [
      "uvp",
      "uvvp"
    ],
    "vnd.dece.sd": [
      "uvs",
      "uvvs"
    ],
    "vnd.dece.video": [
      "uvv",
      "uvvv"
    ],
    "vnd.dvb.file": "dvb",
    "vnd.fvt": "fvt",
    "vnd.ms-playready.media.pyv": "pyv",
    "vnd.uvvu.mp4": [
      "uvu",
      "uvvu"
    ],
    "vnd.vivo": "viv",
    "webm": "webm",
    "x-f4v": "f4v",
    "x-m4v": "m4v",
    "x-ms-vob": "vob",
    "x-smv": "smv",
    "mp2t": "ts"
  },
  "x-conference": {
    "x-cooltalk": "ice"
  },
  "x-world": {
    "x-vrml": [
      "vrm",
      "flr",
      "wrz",
      "xaf",
      "xof"
    ]
  }
};
var mimeTypes = (() => {
  const mimeTypes2 = {};
  for (const type of Object.keys(table)) {
    for (const subtype of Object.keys(table[type])) {
      const value = table[type][subtype];
      if (typeof value == "string") {
        mimeTypes2[value] = type + "/" + subtype;
      } else {
        for (let indexMimeType = 0; indexMimeType < value.length; indexMimeType++) {
          mimeTypes2[value[indexMimeType]] = type + "/" + subtype;
        }
      }
    }
  }
  return mimeTypes2;
})();

// node_modules/@zip.js/zip.js/lib/core/streams/codecs/crc32.js
var table2 = [];
for (let i = 0; i < 256; i++) {
  let t = i;
  for (let j = 0; j < 8; j++) {
    if (t & 1) {
      t = t >>> 1 ^ 3988292384;
    } else {
      t = t >>> 1;
    }
  }
  table2[i] = t;
}
var Crc32 = class {
  constructor(crc) {
    this.crc = crc || -1;
  }
  append(data) {
    let crc = this.crc | 0;
    for (let offset = 0, length = data.length | 0; offset < length; offset++) {
      crc = crc >>> 8 ^ table2[(crc ^ data[offset]) & 255];
    }
    this.crc = crc;
  }
  get() {
    return ~this.crc;
  }
};

// node_modules/@zip.js/zip.js/lib/core/streams/crc32-stream.js
var Crc32Stream = class extends TransformStream {
  constructor() {
    let stream;
    const crc32 = new Crc32();
    super({
      transform(chunk, controller) {
        crc32.append(chunk);
        controller.enqueue(chunk);
      },
      flush() {
        const value = new Uint8Array(4);
        const dataView = new DataView(value.buffer);
        dataView.setUint32(0, crc32.get());
        stream.value = value;
      }
    });
    stream = this;
  }
};

// node_modules/@zip.js/zip.js/lib/core/util/encode-text.js
function encodeText(value) {
  if (typeof TextEncoder == UNDEFINED_TYPE) {
    value = unescape(encodeURIComponent(value));
    const result = new Uint8Array(value.length);
    for (let i = 0; i < result.length; i++) {
      result[i] = value.charCodeAt(i);
    }
    return result;
  } else {
    return new TextEncoder().encode(value);
  }
}

// node_modules/@zip.js/zip.js/lib/core/streams/codecs/sjcl.js
var bitArray = {
  /**
   * Concatenate two bit arrays.
   * @param {bitArray} a1 The first array.
   * @param {bitArray} a2 The second array.
   * @return {bitArray} The concatenation of a1 and a2.
   */
  concat(a1, a2) {
    if (a1.length === 0 || a2.length === 0) {
      return a1.concat(a2);
    }
    const last = a1[a1.length - 1], shift = bitArray.getPartial(last);
    if (shift === 32) {
      return a1.concat(a2);
    } else {
      return bitArray._shiftRight(a2, shift, last | 0, a1.slice(0, a1.length - 1));
    }
  },
  /**
   * Find the length of an array of bits.
   * @param {bitArray} a The array.
   * @return {Number} The length of a, in bits.
   */
  bitLength(a) {
    const l = a.length;
    if (l === 0) {
      return 0;
    }
    const x = a[l - 1];
    return (l - 1) * 32 + bitArray.getPartial(x);
  },
  /**
   * Truncate an array.
   * @param {bitArray} a The array.
   * @param {Number} len The length to truncate to, in bits.
   * @return {bitArray} A new array, truncated to len bits.
   */
  clamp(a, len) {
    if (a.length * 32 < len) {
      return a;
    }
    a = a.slice(0, Math.ceil(len / 32));
    const l = a.length;
    len = len & 31;
    if (l > 0 && len) {
      a[l - 1] = bitArray.partial(len, a[l - 1] & 2147483648 >> len - 1, 1);
    }
    return a;
  },
  /**
   * Make a partial word for a bit array.
   * @param {Number} len The number of bits in the word.
   * @param {Number} x The bits.
   * @param {Number} [_end=0] Pass 1 if x has already been shifted to the high side.
   * @return {Number} The partial word.
   */
  partial(len, x, _end) {
    if (len === 32) {
      return x;
    }
    return (_end ? x | 0 : x << 32 - len) + len * 1099511627776;
  },
  /**
   * Get the number of bits used by a partial word.
   * @param {Number} x The partial word.
   * @return {Number} The number of bits used by the partial word.
   */
  getPartial(x) {
    return Math.round(x / 1099511627776) || 32;
  },
  /** Shift an array right.
   * @param {bitArray} a The array to shift.
   * @param {Number} shift The number of bits to shift.
   * @param {Number} [carry=0] A byte to carry in
   * @param {bitArray} [out=[]] An array to prepend to the output.
   * @private
   */
  _shiftRight(a, shift, carry, out) {
    if (out === void 0) {
      out = [];
    }
    for (; shift >= 32; shift -= 32) {
      out.push(carry);
      carry = 0;
    }
    if (shift === 0) {
      return out.concat(a);
    }
    for (let i = 0; i < a.length; i++) {
      out.push(carry | a[i] >>> shift);
      carry = a[i] << 32 - shift;
    }
    const last2 = a.length ? a[a.length - 1] : 0;
    const shift2 = bitArray.getPartial(last2);
    out.push(bitArray.partial(shift + shift2 & 31, shift + shift2 > 32 ? carry : out.pop(), 1));
    return out;
  }
};
var codec = {
  bytes: {
    /** Convert from a bitArray to an array of bytes. */
    fromBits(arr) {
      const bl = bitArray.bitLength(arr);
      const byteLength = bl / 8;
      const out = new Uint8Array(byteLength);
      let tmp;
      for (let i = 0; i < byteLength; i++) {
        if ((i & 3) === 0) {
          tmp = arr[i / 4];
        }
        out[i] = tmp >>> 24;
        tmp <<= 8;
      }
      return out;
    },
    /** Convert from an array of bytes to a bitArray. */
    toBits(bytes) {
      const out = [];
      let i;
      let tmp = 0;
      for (i = 0; i < bytes.length; i++) {
        tmp = tmp << 8 | bytes[i];
        if ((i & 3) === 3) {
          out.push(tmp);
          tmp = 0;
        }
      }
      if (i & 3) {
        out.push(bitArray.partial(8 * (i & 3), tmp));
      }
      return out;
    }
  }
};
var hash = {};
hash.sha1 = class {
  constructor(hash2) {
    const sha1 = this;
    sha1.blockSize = 512;
    sha1._init = [1732584193, 4023233417, 2562383102, 271733878, 3285377520];
    sha1._key = [1518500249, 1859775393, 2400959708, 3395469782];
    if (hash2) {
      sha1._h = hash2._h.slice(0);
      sha1._buffer = hash2._buffer.slice(0);
      sha1._length = hash2._length;
    } else {
      sha1.reset();
    }
  }
  /**
   * Reset the hash state.
   * @return this
   */
  reset() {
    const sha1 = this;
    sha1._h = sha1._init.slice(0);
    sha1._buffer = [];
    sha1._length = 0;
    return sha1;
  }
  /**
   * Input several words to the hash.
   * @param {bitArray|String} data the data to hash.
   * @return this
   */
  update(data) {
    const sha1 = this;
    if (typeof data === "string") {
      data = codec.utf8String.toBits(data);
    }
    const b = sha1._buffer = bitArray.concat(sha1._buffer, data);
    const ol = sha1._length;
    const nl = sha1._length = ol + bitArray.bitLength(data);
    if (nl > 9007199254740991) {
      throw new Error("Cannot hash more than 2^53 - 1 bits");
    }
    const c = new Uint32Array(b);
    let j = 0;
    for (let i = sha1.blockSize + ol - (sha1.blockSize + ol & sha1.blockSize - 1); i <= nl; i += sha1.blockSize) {
      sha1._block(c.subarray(16 * j, 16 * (j + 1)));
      j += 1;
    }
    b.splice(0, 16 * j);
    return sha1;
  }
  /**
   * Complete hashing and output the hash value.
   * @return {bitArray} The hash value, an array of 5 big-endian words. TODO
   */
  finalize() {
    const sha1 = this;
    let b = sha1._buffer;
    const h = sha1._h;
    b = bitArray.concat(b, [bitArray.partial(1, 1)]);
    for (let i = b.length + 2; i & 15; i++) {
      b.push(0);
    }
    b.push(Math.floor(sha1._length / 4294967296));
    b.push(sha1._length | 0);
    while (b.length) {
      sha1._block(b.splice(0, 16));
    }
    sha1.reset();
    return h;
  }
  /**
   * The SHA-1 logical functions f(0), f(1), ..., f(79).
   * @private
   */
  _f(t, b, c, d) {
    if (t <= 19) {
      return b & c | ~b & d;
    } else if (t <= 39) {
      return b ^ c ^ d;
    } else if (t <= 59) {
      return b & c | b & d | c & d;
    } else if (t <= 79) {
      return b ^ c ^ d;
    }
  }
  /**
   * Circular left-shift operator.
   * @private
   */
  _S(n, x) {
    return x << n | x >>> 32 - n;
  }
  /**
   * Perform one cycle of SHA-1.
   * @param {Uint32Array|bitArray} words one block of words.
   * @private
   */
  _block(words) {
    const sha1 = this;
    const h = sha1._h;
    const w = Array(80);
    for (let j = 0; j < 16; j++) {
      w[j] = words[j];
    }
    let a = h[0];
    let b = h[1];
    let c = h[2];
    let d = h[3];
    let e2 = h[4];
    for (let t = 0; t <= 79; t++) {
      if (t >= 16) {
        w[t] = sha1._S(1, w[t - 3] ^ w[t - 8] ^ w[t - 14] ^ w[t - 16]);
      }
      const tmp = sha1._S(5, a) + sha1._f(t, b, c, d) + e2 + w[t] + sha1._key[Math.floor(t / 20)] | 0;
      e2 = d;
      d = c;
      c = sha1._S(30, b);
      b = a;
      a = tmp;
    }
    h[0] = h[0] + a | 0;
    h[1] = h[1] + b | 0;
    h[2] = h[2] + c | 0;
    h[3] = h[3] + d | 0;
    h[4] = h[4] + e2 | 0;
  }
};
var cipher = {};
cipher.aes = class {
  constructor(key) {
    const aes = this;
    aes._tables = [[[], [], [], [], []], [[], [], [], [], []]];
    if (!aes._tables[0][0][0]) {
      aes._precompute();
    }
    const sbox = aes._tables[0][4];
    const decTable = aes._tables[1];
    const keyLen = key.length;
    let i, encKey, decKey, rcon = 1;
    if (keyLen !== 4 && keyLen !== 6 && keyLen !== 8) {
      throw new Error("invalid aes key size");
    }
    aes._key = [encKey = key.slice(0), decKey = []];
    for (i = keyLen; i < 4 * keyLen + 28; i++) {
      let tmp = encKey[i - 1];
      if (i % keyLen === 0 || keyLen === 8 && i % keyLen === 4) {
        tmp = sbox[tmp >>> 24] << 24 ^ sbox[tmp >> 16 & 255] << 16 ^ sbox[tmp >> 8 & 255] << 8 ^ sbox[tmp & 255];
        if (i % keyLen === 0) {
          tmp = tmp << 8 ^ tmp >>> 24 ^ rcon << 24;
          rcon = rcon << 1 ^ (rcon >> 7) * 283;
        }
      }
      encKey[i] = encKey[i - keyLen] ^ tmp;
    }
    for (let j = 0; i; j++, i--) {
      const tmp = encKey[j & 3 ? i : i - 4];
      if (i <= 4 || j < 4) {
        decKey[j] = tmp;
      } else {
        decKey[j] = decTable[0][sbox[tmp >>> 24]] ^ decTable[1][sbox[tmp >> 16 & 255]] ^ decTable[2][sbox[tmp >> 8 & 255]] ^ decTable[3][sbox[tmp & 255]];
      }
    }
  }
  // public
  /* Something like this might appear here eventually
  name: "AES",
  blockSize: 4,
  keySizes: [4,6,8],
  */
  /**
   * Encrypt an array of 4 big-endian words.
   * @param {Array} data The plaintext.
   * @return {Array} The ciphertext.
   */
  encrypt(data) {
    return this._crypt(data, 0);
  }
  /**
   * Decrypt an array of 4 big-endian words.
   * @param {Array} data The ciphertext.
   * @return {Array} The plaintext.
   */
  decrypt(data) {
    return this._crypt(data, 1);
  }
  /**
   * Expand the S-box tables.
   *
   * @private
   */
  _precompute() {
    const encTable = this._tables[0];
    const decTable = this._tables[1];
    const sbox = encTable[4];
    const sboxInv = decTable[4];
    const d = [];
    const th = [];
    let xInv, x2, x4, x8;
    for (let i = 0; i < 256; i++) {
      th[(d[i] = i << 1 ^ (i >> 7) * 283) ^ i] = i;
    }
    for (let x = xInv = 0; !sbox[x]; x ^= x2 || 1, xInv = th[xInv] || 1) {
      let s = xInv ^ xInv << 1 ^ xInv << 2 ^ xInv << 3 ^ xInv << 4;
      s = s >> 8 ^ s & 255 ^ 99;
      sbox[x] = s;
      sboxInv[s] = x;
      x8 = d[x4 = d[x2 = d[x]]];
      let tDec = x8 * 16843009 ^ x4 * 65537 ^ x2 * 257 ^ x * 16843008;
      let tEnc = d[s] * 257 ^ s * 16843008;
      for (let i = 0; i < 4; i++) {
        encTable[i][x] = tEnc = tEnc << 24 ^ tEnc >>> 8;
        decTable[i][s] = tDec = tDec << 24 ^ tDec >>> 8;
      }
    }
    for (let i = 0; i < 5; i++) {
      encTable[i] = encTable[i].slice(0);
      decTable[i] = decTable[i].slice(0);
    }
  }
  /**
   * Encryption and decryption core.
   * @param {Array} input Four words to be encrypted or decrypted.
   * @param dir The direction, 0 for encrypt and 1 for decrypt.
   * @return {Array} The four encrypted or decrypted words.
   * @private
   */
  _crypt(input, dir) {
    if (input.length !== 4) {
      throw new Error("invalid aes block size");
    }
    const key = this._key[dir];
    const nInnerRounds = key.length / 4 - 2;
    const out = [0, 0, 0, 0];
    const table3 = this._tables[dir];
    const t0 = table3[0];
    const t1 = table3[1];
    const t2 = table3[2];
    const t3 = table3[3];
    const sbox = table3[4];
    let a = input[0] ^ key[0];
    let b = input[dir ? 3 : 1] ^ key[1];
    let c = input[2] ^ key[2];
    let d = input[dir ? 1 : 3] ^ key[3];
    let kIndex = 4;
    let a2, b2, c2;
    for (let i = 0; i < nInnerRounds; i++) {
      a2 = t0[a >>> 24] ^ t1[b >> 16 & 255] ^ t2[c >> 8 & 255] ^ t3[d & 255] ^ key[kIndex];
      b2 = t0[b >>> 24] ^ t1[c >> 16 & 255] ^ t2[d >> 8 & 255] ^ t3[a & 255] ^ key[kIndex + 1];
      c2 = t0[c >>> 24] ^ t1[d >> 16 & 255] ^ t2[a >> 8 & 255] ^ t3[b & 255] ^ key[kIndex + 2];
      d = t0[d >>> 24] ^ t1[a >> 16 & 255] ^ t2[b >> 8 & 255] ^ t3[c & 255] ^ key[kIndex + 3];
      kIndex += 4;
      a = a2;
      b = b2;
      c = c2;
    }
    for (let i = 0; i < 4; i++) {
      out[dir ? 3 & -i : i] = sbox[a >>> 24] << 24 ^ sbox[b >> 16 & 255] << 16 ^ sbox[c >> 8 & 255] << 8 ^ sbox[d & 255] ^ key[kIndex++];
      a2 = a;
      a = b;
      b = c;
      c = d;
      d = a2;
    }
    return out;
  }
};
var random = {
  /** 
   * Generate random words with pure js, cryptographically not as strong & safe as native implementation.
   * @param {TypedArray} typedArray The array to fill.
   * @return {TypedArray} The random values.
   */
  getRandomValues(typedArray) {
    const words = new Uint32Array(typedArray.buffer);
    const r = (m_w) => {
      let m_z = 987654321;
      const mask = 4294967295;
      return function() {
        m_z = 36969 * (m_z & 65535) + (m_z >> 16) & mask;
        m_w = 18e3 * (m_w & 65535) + (m_w >> 16) & mask;
        const result = ((m_z << 16) + m_w & mask) / 4294967296 + 0.5;
        return result * (Math.random() > 0.5 ? 1 : -1);
      };
    };
    for (let i = 0, rcache; i < typedArray.length; i += 4) {
      const _r = r((rcache || Math.random()) * 4294967296);
      rcache = _r() * 987654071;
      words[i / 4] = _r() * 4294967296 | 0;
    }
    return typedArray;
  }
};
var mode = {};
mode.ctrGladman = class {
  constructor(prf, iv) {
    this._prf = prf;
    this._initIv = iv;
    this._iv = iv;
  }
  reset() {
    this._iv = this._initIv;
  }
  /** Input some data to calculate.
   * @param {bitArray} data the data to process, it must be intergral multiple of 128 bits unless it's the last.
   */
  update(data) {
    return this.calculate(this._prf, data, this._iv);
  }
  incWord(word) {
    if ((word >> 24 & 255) === 255) {
      let b1 = word >> 16 & 255;
      let b2 = word >> 8 & 255;
      let b3 = word & 255;
      if (b1 === 255) {
        b1 = 0;
        if (b2 === 255) {
          b2 = 0;
          if (b3 === 255) {
            b3 = 0;
          } else {
            ++b3;
          }
        } else {
          ++b2;
        }
      } else {
        ++b1;
      }
      word = 0;
      word += b1 << 16;
      word += b2 << 8;
      word += b3;
    } else {
      word += 1 << 24;
    }
    return word;
  }
  incCounter(counter) {
    if ((counter[0] = this.incWord(counter[0])) === 0) {
      counter[1] = this.incWord(counter[1]);
    }
  }
  calculate(prf, data, iv) {
    let l;
    if (!(l = data.length)) {
      return [];
    }
    const bl = bitArray.bitLength(data);
    for (let i = 0; i < l; i += 4) {
      this.incCounter(iv);
      const e2 = prf.encrypt(iv);
      data[i] ^= e2[0];
      data[i + 1] ^= e2[1];
      data[i + 2] ^= e2[2];
      data[i + 3] ^= e2[3];
    }
    return bitArray.clamp(data, bl);
  }
};
var misc = {
  importKey(password) {
    return new misc.hmacSha1(codec.bytes.toBits(password));
  },
  pbkdf2(prf, salt, count, length) {
    count = count || 1e4;
    if (length < 0 || count < 0) {
      throw new Error("invalid params to pbkdf2");
    }
    const byteLength = (length >> 5) + 1 << 2;
    let u, ui, i, j, k;
    const arrayBuffer = new ArrayBuffer(byteLength);
    const out = new DataView(arrayBuffer);
    let outLength = 0;
    const b = bitArray;
    salt = codec.bytes.toBits(salt);
    for (k = 1; outLength < (byteLength || 1); k++) {
      u = ui = prf.encrypt(b.concat(salt, [k]));
      for (i = 1; i < count; i++) {
        ui = prf.encrypt(ui);
        for (j = 0; j < ui.length; j++) {
          u[j] ^= ui[j];
        }
      }
      for (i = 0; outLength < (byteLength || 1) && i < u.length; i++) {
        out.setInt32(outLength, u[i]);
        outLength += 4;
      }
    }
    return arrayBuffer.slice(0, length / 8);
  }
};
misc.hmacSha1 = class {
  constructor(key) {
    const hmac = this;
    const Hash = hmac._hash = hash.sha1;
    const exKey = [[], []];
    hmac._baseHash = [new Hash(), new Hash()];
    const bs = hmac._baseHash[0].blockSize / 32;
    if (key.length > bs) {
      key = new Hash().update(key).finalize();
    }
    for (let i = 0; i < bs; i++) {
      exKey[0][i] = key[i] ^ 909522486;
      exKey[1][i] = key[i] ^ 1549556828;
    }
    hmac._baseHash[0].update(exKey[0]);
    hmac._baseHash[1].update(exKey[1]);
    hmac._resultHash = new Hash(hmac._baseHash[0]);
  }
  reset() {
    const hmac = this;
    hmac._resultHash = new hmac._hash(hmac._baseHash[0]);
    hmac._updated = false;
  }
  update(data) {
    const hmac = this;
    hmac._updated = true;
    hmac._resultHash.update(data);
  }
  digest() {
    const hmac = this;
    const w = hmac._resultHash.finalize();
    const result = new hmac._hash(hmac._baseHash[1]).update(w).finalize();
    hmac.reset();
    return result;
  }
  encrypt(data) {
    if (!this._updated) {
      this.update(data);
      return this.digest(data);
    } else {
      throw new Error("encrypt on already updated hmac called!");
    }
  }
};

// node_modules/@zip.js/zip.js/lib/core/streams/common-crypto.js
var GET_RANDOM_VALUES_SUPPORTED = typeof crypto != UNDEFINED_TYPE && typeof crypto.getRandomValues == FUNCTION_TYPE;
var ERR_INVALID_PASSWORD = "Invalid password";
var ERR_INVALID_SIGNATURE = "Invalid signature";
var ERR_ABORT_CHECK_PASSWORD = "zipjs-abort-check-password";
function getRandomValues(array) {
  if (GET_RANDOM_VALUES_SUPPORTED) {
    return crypto.getRandomValues(array);
  } else {
    return random.getRandomValues(array);
  }
}

// node_modules/@zip.js/zip.js/lib/core/streams/aes-crypto-stream.js
var BLOCK_LENGTH = 16;
var RAW_FORMAT = "raw";
var PBKDF2_ALGORITHM = { name: "PBKDF2" };
var HASH_ALGORITHM = { name: "HMAC" };
var HASH_FUNCTION = "SHA-1";
var BASE_KEY_ALGORITHM = Object.assign({ hash: HASH_ALGORITHM }, PBKDF2_ALGORITHM);
var DERIVED_BITS_ALGORITHM = Object.assign({ iterations: 1e3, hash: { name: HASH_FUNCTION } }, PBKDF2_ALGORITHM);
var DERIVED_BITS_USAGE = ["deriveBits"];
var SALT_LENGTH = [8, 12, 16];
var KEY_LENGTH = [16, 24, 32];
var SIGNATURE_LENGTH = 10;
var COUNTER_DEFAULT_VALUE = [0, 0, 0, 0];
var CRYPTO_API_SUPPORTED = typeof crypto != UNDEFINED_TYPE;
var subtle = CRYPTO_API_SUPPORTED && crypto.subtle;
var SUBTLE_API_SUPPORTED = CRYPTO_API_SUPPORTED && typeof subtle != UNDEFINED_TYPE;
var codecBytes = codec.bytes;
var Aes = cipher.aes;
var CtrGladman = mode.ctrGladman;
var HmacSha1 = misc.hmacSha1;
var IMPORT_KEY_SUPPORTED = CRYPTO_API_SUPPORTED && SUBTLE_API_SUPPORTED && typeof subtle.importKey == FUNCTION_TYPE;
var DERIVE_BITS_SUPPORTED = CRYPTO_API_SUPPORTED && SUBTLE_API_SUPPORTED && typeof subtle.deriveBits == FUNCTION_TYPE;
var AESDecryptionStream = class extends TransformStream {
  constructor({ password, rawPassword, signed, encryptionStrength, checkPasswordOnly }) {
    super({
      start() {
        Object.assign(this, {
          ready: new Promise((resolve) => this.resolveReady = resolve),
          password: encodePassword(password, rawPassword),
          signed,
          strength: encryptionStrength - 1,
          pending: new Uint8Array()
        });
      },
      async transform(chunk, controller) {
        const aesCrypto = this;
        const {
          password: password2,
          strength,
          resolveReady,
          ready
        } = aesCrypto;
        if (password2) {
          await createDecryptionKeys(aesCrypto, strength, password2, subarray(chunk, 0, SALT_LENGTH[strength] + 2));
          chunk = subarray(chunk, SALT_LENGTH[strength] + 2);
          if (checkPasswordOnly) {
            controller.error(new Error(ERR_ABORT_CHECK_PASSWORD));
          } else {
            resolveReady();
          }
        } else {
          await ready;
        }
        const output = new Uint8Array(chunk.length - SIGNATURE_LENGTH - (chunk.length - SIGNATURE_LENGTH) % BLOCK_LENGTH);
        controller.enqueue(append(aesCrypto, chunk, output, 0, SIGNATURE_LENGTH, true));
      },
      async flush(controller) {
        const {
          signed: signed2,
          ctr,
          hmac,
          pending,
          ready
        } = this;
        if (hmac && ctr) {
          await ready;
          const chunkToDecrypt = subarray(pending, 0, pending.length - SIGNATURE_LENGTH);
          const originalSignature = subarray(pending, pending.length - SIGNATURE_LENGTH);
          let decryptedChunkArray = new Uint8Array();
          if (chunkToDecrypt.length) {
            const encryptedChunk = toBits(codecBytes, chunkToDecrypt);
            hmac.update(encryptedChunk);
            const decryptedChunk = ctr.update(encryptedChunk);
            decryptedChunkArray = fromBits(codecBytes, decryptedChunk);
          }
          if (signed2) {
            const signature = subarray(fromBits(codecBytes, hmac.digest()), 0, SIGNATURE_LENGTH);
            for (let indexSignature = 0; indexSignature < SIGNATURE_LENGTH; indexSignature++) {
              if (signature[indexSignature] != originalSignature[indexSignature]) {
                throw new Error(ERR_INVALID_SIGNATURE);
              }
            }
          }
          controller.enqueue(decryptedChunkArray);
        }
      }
    });
  }
};
var AESEncryptionStream = class extends TransformStream {
  constructor({ password, rawPassword, encryptionStrength }) {
    let stream;
    super({
      start() {
        Object.assign(this, {
          ready: new Promise((resolve) => this.resolveReady = resolve),
          password: encodePassword(password, rawPassword),
          strength: encryptionStrength - 1,
          pending: new Uint8Array()
        });
      },
      async transform(chunk, controller) {
        const aesCrypto = this;
        const {
          password: password2,
          strength,
          resolveReady,
          ready
        } = aesCrypto;
        let preamble = new Uint8Array();
        if (password2) {
          preamble = await createEncryptionKeys(aesCrypto, strength, password2);
          resolveReady();
        } else {
          await ready;
        }
        const output = new Uint8Array(preamble.length + chunk.length - chunk.length % BLOCK_LENGTH);
        output.set(preamble, 0);
        controller.enqueue(append(aesCrypto, chunk, output, preamble.length, 0));
      },
      async flush(controller) {
        const {
          ctr,
          hmac,
          pending,
          ready
        } = this;
        if (hmac && ctr) {
          await ready;
          let encryptedChunkArray = new Uint8Array();
          if (pending.length) {
            const encryptedChunk = ctr.update(toBits(codecBytes, pending));
            hmac.update(encryptedChunk);
            encryptedChunkArray = fromBits(codecBytes, encryptedChunk);
          }
          stream.signature = fromBits(codecBytes, hmac.digest()).slice(0, SIGNATURE_LENGTH);
          controller.enqueue(concat(encryptedChunkArray, stream.signature));
        }
      }
    });
    stream = this;
  }
};
function append(aesCrypto, input, output, paddingStart, paddingEnd, verifySignature) {
  const {
    ctr,
    hmac,
    pending
  } = aesCrypto;
  const inputLength = input.length - paddingEnd;
  if (pending.length) {
    input = concat(pending, input);
    output = expand(output, inputLength - inputLength % BLOCK_LENGTH);
  }
  let offset;
  for (offset = 0; offset <= inputLength - BLOCK_LENGTH; offset += BLOCK_LENGTH) {
    const inputChunk = toBits(codecBytes, subarray(input, offset, offset + BLOCK_LENGTH));
    if (verifySignature) {
      hmac.update(inputChunk);
    }
    const outputChunk = ctr.update(inputChunk);
    if (!verifySignature) {
      hmac.update(outputChunk);
    }
    output.set(fromBits(codecBytes, outputChunk), offset + paddingStart);
  }
  aesCrypto.pending = subarray(input, offset);
  return output;
}
async function createDecryptionKeys(decrypt2, strength, password, preamble) {
  const passwordVerificationKey = await createKeys(decrypt2, strength, password, subarray(preamble, 0, SALT_LENGTH[strength]));
  const passwordVerification = subarray(preamble, SALT_LENGTH[strength]);
  if (passwordVerificationKey[0] != passwordVerification[0] || passwordVerificationKey[1] != passwordVerification[1]) {
    throw new Error(ERR_INVALID_PASSWORD);
  }
}
async function createEncryptionKeys(encrypt2, strength, password) {
  const salt = getRandomValues(new Uint8Array(SALT_LENGTH[strength]));
  const passwordVerification = await createKeys(encrypt2, strength, password, salt);
  return concat(salt, passwordVerification);
}
async function createKeys(aesCrypto, strength, password, salt) {
  aesCrypto.password = null;
  const baseKey = await importKey(RAW_FORMAT, password, BASE_KEY_ALGORITHM, false, DERIVED_BITS_USAGE);
  const derivedBits = await deriveBits(Object.assign({ salt }, DERIVED_BITS_ALGORITHM), baseKey, 8 * (KEY_LENGTH[strength] * 2 + 2));
  const compositeKey = new Uint8Array(derivedBits);
  const key = toBits(codecBytes, subarray(compositeKey, 0, KEY_LENGTH[strength]));
  const authentication = toBits(codecBytes, subarray(compositeKey, KEY_LENGTH[strength], KEY_LENGTH[strength] * 2));
  const passwordVerification = subarray(compositeKey, KEY_LENGTH[strength] * 2);
  Object.assign(aesCrypto, {
    keys: {
      key,
      authentication,
      passwordVerification
    },
    ctr: new CtrGladman(new Aes(key), Array.from(COUNTER_DEFAULT_VALUE)),
    hmac: new HmacSha1(authentication)
  });
  return passwordVerification;
}
async function importKey(format, password, algorithm, extractable, keyUsages) {
  if (IMPORT_KEY_SUPPORTED) {
    try {
      return await subtle.importKey(format, password, algorithm, extractable, keyUsages);
    } catch (_) {
      IMPORT_KEY_SUPPORTED = false;
      return misc.importKey(password);
    }
  } else {
    return misc.importKey(password);
  }
}
async function deriveBits(algorithm, baseKey, length) {
  if (DERIVE_BITS_SUPPORTED) {
    try {
      return await subtle.deriveBits(algorithm, baseKey, length);
    } catch (_) {
      DERIVE_BITS_SUPPORTED = false;
      return misc.pbkdf2(baseKey, algorithm.salt, DERIVED_BITS_ALGORITHM.iterations, length);
    }
  } else {
    return misc.pbkdf2(baseKey, algorithm.salt, DERIVED_BITS_ALGORITHM.iterations, length);
  }
}
function encodePassword(password, rawPassword) {
  if (rawPassword === UNDEFINED_VALUE) {
    return encodeText(password);
  } else {
    return rawPassword;
  }
}
function concat(leftArray, rightArray) {
  let array = leftArray;
  if (leftArray.length + rightArray.length) {
    array = new Uint8Array(leftArray.length + rightArray.length);
    array.set(leftArray, 0);
    array.set(rightArray, leftArray.length);
  }
  return array;
}
function expand(inputArray, length) {
  if (length && length > inputArray.length) {
    const array = inputArray;
    inputArray = new Uint8Array(length);
    inputArray.set(array, 0);
  }
  return inputArray;
}
function subarray(array, begin, end) {
  return array.subarray(begin, end);
}
function fromBits(codecBytes2, chunk) {
  return codecBytes2.fromBits(chunk);
}
function toBits(codecBytes2, chunk) {
  return codecBytes2.toBits(chunk);
}

// node_modules/@zip.js/zip.js/lib/core/streams/zip-crypto-stream.js
var HEADER_LENGTH = 12;
var ZipCryptoDecryptionStream = class extends TransformStream {
  constructor({ password, passwordVerification, checkPasswordOnly }) {
    super({
      start() {
        Object.assign(this, {
          password,
          passwordVerification
        });
        createKeys2(this, password);
      },
      transform(chunk, controller) {
        const zipCrypto = this;
        if (zipCrypto.password) {
          const decryptedHeader = decrypt(zipCrypto, chunk.subarray(0, HEADER_LENGTH));
          zipCrypto.password = null;
          if (decryptedHeader[HEADER_LENGTH - 1] != zipCrypto.passwordVerification) {
            throw new Error(ERR_INVALID_PASSWORD);
          }
          chunk = chunk.subarray(HEADER_LENGTH);
        }
        if (checkPasswordOnly) {
          controller.error(new Error(ERR_ABORT_CHECK_PASSWORD));
        } else {
          controller.enqueue(decrypt(zipCrypto, chunk));
        }
      }
    });
  }
};
var ZipCryptoEncryptionStream = class extends TransformStream {
  constructor({ password, passwordVerification }) {
    super({
      start() {
        Object.assign(this, {
          password,
          passwordVerification
        });
        createKeys2(this, password);
      },
      transform(chunk, controller) {
        const zipCrypto = this;
        let output;
        let offset;
        if (zipCrypto.password) {
          zipCrypto.password = null;
          const header = getRandomValues(new Uint8Array(HEADER_LENGTH));
          header[HEADER_LENGTH - 1] = zipCrypto.passwordVerification;
          output = new Uint8Array(chunk.length + header.length);
          output.set(encrypt(zipCrypto, header), 0);
          offset = HEADER_LENGTH;
        } else {
          output = new Uint8Array(chunk.length);
          offset = 0;
        }
        output.set(encrypt(zipCrypto, chunk), offset);
        controller.enqueue(output);
      }
    });
  }
};
function decrypt(target, input) {
  const output = new Uint8Array(input.length);
  for (let index = 0; index < input.length; index++) {
    output[index] = getByte(target) ^ input[index];
    updateKeys(target, output[index]);
  }
  return output;
}
function encrypt(target, input) {
  const output = new Uint8Array(input.length);
  for (let index = 0; index < input.length; index++) {
    output[index] = getByte(target) ^ input[index];
    updateKeys(target, input[index]);
  }
  return output;
}
function createKeys2(target, password) {
  const keys = [305419896, 591751049, 878082192];
  Object.assign(target, {
    keys,
    crcKey0: new Crc32(keys[0]),
    crcKey2: new Crc32(keys[2])
  });
  for (let index = 0; index < password.length; index++) {
    updateKeys(target, password.charCodeAt(index));
  }
}
function updateKeys(target, byte) {
  let [key0, key1, key2] = target.keys;
  target.crcKey0.append([byte]);
  key0 = ~target.crcKey0.get();
  key1 = getInt32(Math.imul(getInt32(key1 + getInt8(key0)), 134775813) + 1);
  target.crcKey2.append([key1 >>> 24]);
  key2 = ~target.crcKey2.get();
  target.keys = [key0, key1, key2];
}
function getByte(target) {
  const temp = target.keys[2] | 2;
  return getInt8(Math.imul(temp, temp ^ 1) >>> 8);
}
function getInt8(number) {
  return number & 255;
}
function getInt32(number) {
  return number & 4294967295;
}

// node_modules/@zip.js/zip.js/lib/core/streams/zip-entry-stream.js
var COMPRESSION_FORMAT = "deflate-raw";
var DeflateStream = class extends TransformStream {
  constructor(options, { chunkSize, CompressionStream: CompressionStream2, CompressionStreamNative }) {
    super({});
    const { compressed, encrypted, useCompressionStream, zipCrypto, signed, level } = options;
    const stream = this;
    let crc32Stream, encryptionStream;
    let readable = filterEmptyChunks(super.readable);
    if ((!encrypted || zipCrypto) && signed) {
      crc32Stream = new Crc32Stream();
      readable = pipeThrough(readable, crc32Stream);
    }
    if (compressed) {
      readable = pipeThroughCommpressionStream(readable, useCompressionStream, { level, chunkSize }, CompressionStreamNative, CompressionStream2);
    }
    if (encrypted) {
      if (zipCrypto) {
        readable = pipeThrough(readable, new ZipCryptoEncryptionStream(options));
      } else {
        encryptionStream = new AESEncryptionStream(options);
        readable = pipeThrough(readable, encryptionStream);
      }
    }
    setReadable(stream, readable, () => {
      let signature;
      if (encrypted && !zipCrypto) {
        signature = encryptionStream.signature;
      }
      if ((!encrypted || zipCrypto) && signed) {
        signature = new DataView(crc32Stream.value.buffer).getUint32(0);
      }
      stream.signature = signature;
    });
  }
};
var InflateStream = class extends TransformStream {
  constructor(options, { chunkSize, DecompressionStream: DecompressionStream2, DecompressionStreamNative }) {
    super({});
    const { zipCrypto, encrypted, signed, signature, compressed, useCompressionStream } = options;
    let crc32Stream, decryptionStream;
    let readable = filterEmptyChunks(super.readable);
    if (encrypted) {
      if (zipCrypto) {
        readable = pipeThrough(readable, new ZipCryptoDecryptionStream(options));
      } else {
        decryptionStream = new AESDecryptionStream(options);
        readable = pipeThrough(readable, decryptionStream);
      }
    }
    if (compressed) {
      readable = pipeThroughCommpressionStream(readable, useCompressionStream, { chunkSize }, DecompressionStreamNative, DecompressionStream2);
    }
    if ((!encrypted || zipCrypto) && signed) {
      crc32Stream = new Crc32Stream();
      readable = pipeThrough(readable, crc32Stream);
    }
    setReadable(this, readable, () => {
      if ((!encrypted || zipCrypto) && signed) {
        const dataViewSignature = new DataView(crc32Stream.value.buffer);
        if (signature != dataViewSignature.getUint32(0, false)) {
          throw new Error(ERR_INVALID_SIGNATURE);
        }
      }
    });
  }
};
function filterEmptyChunks(readable) {
  return pipeThrough(readable, new TransformStream({
    transform(chunk, controller) {
      if (chunk && chunk.length) {
        controller.enqueue(chunk);
      }
    }
  }));
}
function setReadable(stream, readable, flush) {
  readable = pipeThrough(readable, new TransformStream({ flush }));
  Object.defineProperty(stream, "readable", {
    get() {
      return readable;
    }
  });
}
function pipeThroughCommpressionStream(readable, useCompressionStream, options, CodecStreamNative, CodecStream2) {
  try {
    const CompressionStream2 = useCompressionStream && CodecStreamNative ? CodecStreamNative : CodecStream2;
    readable = pipeThrough(readable, new CompressionStream2(COMPRESSION_FORMAT, options));
  } catch (_) {
    if (useCompressionStream) {
      try {
        readable = pipeThrough(readable, new CodecStream2(COMPRESSION_FORMAT, options));
      } catch (_2) {
        return readable;
      }
    } else {
      return readable;
    }
  }
  return readable;
}
function pipeThrough(readable, transformStream) {
  return readable.pipeThrough(transformStream);
}

// node_modules/@zip.js/zip.js/lib/core/streams/codec-stream.js
var MESSAGE_EVENT_TYPE = "message";
var MESSAGE_START = "start";
var MESSAGE_PULL = "pull";
var MESSAGE_DATA = "data";
var MESSAGE_ACK_DATA = "ack";
var MESSAGE_CLOSE = "close";
var CODEC_DEFLATE = "deflate";
var CODEC_INFLATE = "inflate";
var CodecStream = class extends TransformStream {
  constructor(options, config2) {
    super({});
    const codec2 = this;
    const { codecType } = options;
    let Stream2;
    if (codecType.startsWith(CODEC_DEFLATE)) {
      Stream2 = DeflateStream;
    } else if (codecType.startsWith(CODEC_INFLATE)) {
      Stream2 = InflateStream;
    }
    let outputSize = 0;
    let inputSize = 0;
    const stream = new Stream2(options, config2);
    const readable = super.readable;
    const inputSizeStream = new TransformStream({
      transform(chunk, controller) {
        if (chunk && chunk.length) {
          inputSize += chunk.length;
          controller.enqueue(chunk);
        }
      },
      flush() {
        Object.assign(codec2, {
          inputSize
        });
      }
    });
    const outputSizeStream = new TransformStream({
      transform(chunk, controller) {
        if (chunk && chunk.length) {
          outputSize += chunk.length;
          controller.enqueue(chunk);
        }
      },
      flush() {
        const { signature } = stream;
        Object.assign(codec2, {
          signature,
          outputSize,
          inputSize
        });
      }
    });
    Object.defineProperty(codec2, "readable", {
      get() {
        return readable.pipeThrough(inputSizeStream).pipeThrough(stream).pipeThrough(outputSizeStream);
      }
    });
  }
};
var ChunkStream = class extends TransformStream {
  constructor(chunkSize) {
    let pendingChunk;
    super({
      transform,
      flush(controller) {
        if (pendingChunk && pendingChunk.length) {
          controller.enqueue(pendingChunk);
        }
      }
    });
    function transform(chunk, controller) {
      if (pendingChunk) {
        const newChunk = new Uint8Array(pendingChunk.length + chunk.length);
        newChunk.set(pendingChunk);
        newChunk.set(chunk, pendingChunk.length);
        chunk = newChunk;
        pendingChunk = null;
      }
      if (chunk.length > chunkSize) {
        controller.enqueue(chunk.slice(0, chunkSize));
        transform(chunk.slice(chunkSize), controller);
      } else {
        pendingChunk = chunk;
      }
    }
  }
};

// node_modules/@zip.js/zip.js/lib/core/codec-worker.js
var WEB_WORKERS_SUPPORTED = typeof Worker != UNDEFINED_TYPE;
var CodecWorker = class {
  constructor(workerData, { readable, writable }, { options, config: config2, streamOptions, useWebWorkers, transferStreams, scripts }, onTaskFinished) {
    const { signal } = streamOptions;
    Object.assign(workerData, {
      busy: true,
      readable: readable.pipeThrough(new ChunkStream(config2.chunkSize)).pipeThrough(new ProgressWatcherStream(readable, streamOptions), { signal }),
      writable,
      options: Object.assign({}, options),
      scripts,
      transferStreams,
      terminate() {
        return new Promise((resolve) => {
          const { worker, busy } = workerData;
          if (worker) {
            if (busy) {
              workerData.resolveTerminated = resolve;
            } else {
              worker.terminate();
              resolve();
            }
            workerData.interface = null;
          } else {
            resolve();
          }
        });
      },
      onTaskFinished() {
        const { resolveTerminated } = workerData;
        if (resolveTerminated) {
          workerData.resolveTerminated = null;
          workerData.terminated = true;
          workerData.worker.terminate();
          resolveTerminated();
        }
        workerData.busy = false;
        onTaskFinished(workerData);
      }
    });
    return (useWebWorkers && WEB_WORKERS_SUPPORTED ? createWebWorkerInterface : createWorkerInterface)(workerData, config2);
  }
};
var ProgressWatcherStream = class extends TransformStream {
  constructor(readableSource, { onstart, onprogress, size, onend }) {
    let chunkOffset = 0;
    super({
      async start() {
        if (onstart) {
          await callHandler(onstart, size);
        }
      },
      async transform(chunk, controller) {
        chunkOffset += chunk.length;
        if (onprogress) {
          await callHandler(onprogress, chunkOffset, size);
        }
        controller.enqueue(chunk);
      },
      async flush() {
        readableSource.size = chunkOffset;
        if (onend) {
          await callHandler(onend, chunkOffset);
        }
      }
    });
  }
};
async function callHandler(handler, ...parameters) {
  try {
    await handler(...parameters);
  } catch (_) {
  }
}
function createWorkerInterface(workerData, config2) {
  return {
    run: () => runWorker(workerData, config2)
  };
}
function createWebWorkerInterface(workerData, config2) {
  const { baseURL: baseURL2, chunkSize } = config2;
  if (!workerData.interface) {
    let worker;
    try {
      worker = getWebWorker(workerData.scripts[0], baseURL2, workerData);
    } catch (_) {
      WEB_WORKERS_SUPPORTED = false;
      return createWorkerInterface(workerData, config2);
    }
    Object.assign(workerData, {
      worker,
      interface: {
        run: () => runWebWorker(workerData, { chunkSize })
      }
    });
  }
  return workerData.interface;
}
async function runWorker({ options, readable, writable, onTaskFinished }, config2) {
  try {
    const codecStream = new CodecStream(options, config2);
    await readable.pipeThrough(codecStream).pipeTo(writable, { preventClose: true, preventAbort: true });
    const {
      signature,
      inputSize,
      outputSize
    } = codecStream;
    return {
      signature,
      inputSize,
      outputSize
    };
  } finally {
    onTaskFinished();
  }
}
async function runWebWorker(workerData, config2) {
  let resolveResult, rejectResult;
  const result = new Promise((resolve, reject) => {
    resolveResult = resolve;
    rejectResult = reject;
  });
  Object.assign(workerData, {
    reader: null,
    writer: null,
    resolveResult,
    rejectResult,
    result
  });
  const { readable, options, scripts } = workerData;
  const { writable, closed } = watchClosedStream(workerData.writable);
  const streamsTransferred = sendMessage({
    type: MESSAGE_START,
    scripts: scripts.slice(1),
    options,
    config: config2,
    readable,
    writable
  }, workerData);
  if (!streamsTransferred) {
    Object.assign(workerData, {
      reader: readable.getReader(),
      writer: writable.getWriter()
    });
  }
  const resultValue = await result;
  if (!streamsTransferred) {
    await writable.getWriter().close();
  }
  await closed;
  return resultValue;
}
function watchClosedStream(writableSource) {
  let resolveStreamClosed;
  const closed = new Promise((resolve) => resolveStreamClosed = resolve);
  const writable = new WritableStream({
    async write(chunk) {
      const writer = writableSource.getWriter();
      await writer.ready;
      await writer.write(chunk);
      writer.releaseLock();
    },
    close() {
      resolveStreamClosed();
    },
    abort(reason) {
      const writer = writableSource.getWriter();
      return writer.abort(reason);
    }
  });
  return { writable, closed };
}
var classicWorkersSupported = true;
var transferStreamsSupported = true;
function getWebWorker(url, baseURL2, workerData) {
  const workerOptions = { type: "module" };
  let scriptUrl, worker;
  if (typeof url == FUNCTION_TYPE) {
    url = url();
  }
  try {
    scriptUrl = new URL(url, baseURL2);
  } catch (_) {
    scriptUrl = url;
  }
  if (classicWorkersSupported) {
    try {
      worker = new Worker(scriptUrl);
    } catch (_) {
      classicWorkersSupported = false;
      worker = new Worker(scriptUrl, workerOptions);
    }
  } else {
    worker = new Worker(scriptUrl, workerOptions);
  }
  worker.addEventListener(MESSAGE_EVENT_TYPE, (event) => onMessage(event, workerData));
  return worker;
}
function sendMessage(message, { worker, writer, onTaskFinished, transferStreams }) {
  try {
    const { value, readable, writable } = message;
    const transferables = [];
    if (value) {
      if (value.byteLength < value.buffer.byteLength) {
        message.value = value.buffer.slice(0, value.byteLength);
      } else {
        message.value = value.buffer;
      }
      transferables.push(message.value);
    }
    if (transferStreams && transferStreamsSupported) {
      if (readable) {
        transferables.push(readable);
      }
      if (writable) {
        transferables.push(writable);
      }
    } else {
      message.readable = message.writable = null;
    }
    if (transferables.length) {
      try {
        worker.postMessage(message, transferables);
        return true;
      } catch (_) {
        transferStreamsSupported = false;
        message.readable = message.writable = null;
        worker.postMessage(message);
      }
    } else {
      worker.postMessage(message);
    }
  } catch (error) {
    if (writer) {
      writer.releaseLock();
    }
    onTaskFinished();
    throw error;
  }
}
async function onMessage({ data }, workerData) {
  const { type, value, messageId, result, error } = data;
  const { reader, writer, resolveResult, rejectResult, onTaskFinished } = workerData;
  try {
    if (error) {
      const { message, stack, code, name } = error;
      const responseError = new Error(message);
      Object.assign(responseError, { stack, code, name });
      close(responseError);
    } else {
      if (type == MESSAGE_PULL) {
        const { value: value2, done } = await reader.read();
        sendMessage({ type: MESSAGE_DATA, value: value2, done, messageId }, workerData);
      }
      if (type == MESSAGE_DATA) {
        await writer.ready;
        await writer.write(new Uint8Array(value));
        sendMessage({ type: MESSAGE_ACK_DATA, messageId }, workerData);
      }
      if (type == MESSAGE_CLOSE) {
        close(null, result);
      }
    }
  } catch (error2) {
    sendMessage({ type: MESSAGE_CLOSE, messageId }, workerData);
    close(error2);
  }
  function close(error2, result2) {
    if (error2) {
      rejectResult(error2);
    } else {
      resolveResult(result2);
    }
    if (writer) {
      writer.releaseLock();
    }
    onTaskFinished();
  }
}

// node_modules/@zip.js/zip.js/lib/core/codec-pool.js
var pool = [];
var pendingRequests = [];
var indexWorker = 0;
async function runWorker2(stream, workerOptions) {
  const { options, config: config2 } = workerOptions;
  const { transferStreams, useWebWorkers, useCompressionStream, codecType, compressed, signed, encrypted } = options;
  const { workerScripts, maxWorkers: maxWorkers2 } = config2;
  workerOptions.transferStreams = transferStreams || transferStreams === UNDEFINED_VALUE;
  const streamCopy = !compressed && !signed && !encrypted && !workerOptions.transferStreams;
  workerOptions.useWebWorkers = !streamCopy && (useWebWorkers || useWebWorkers === UNDEFINED_VALUE && config2.useWebWorkers);
  workerOptions.scripts = workerOptions.useWebWorkers && workerScripts ? workerScripts[codecType] : [];
  options.useCompressionStream = useCompressionStream || useCompressionStream === UNDEFINED_VALUE && config2.useCompressionStream;
  return (await getWorker()).run();
  async function getWorker() {
    const workerData = pool.find((workerData2) => !workerData2.busy);
    if (workerData) {
      clearTerminateTimeout(workerData);
      return new CodecWorker(workerData, stream, workerOptions, onTaskFinished);
    } else if (pool.length < maxWorkers2) {
      const workerData2 = { indexWorker };
      indexWorker++;
      pool.push(workerData2);
      return new CodecWorker(workerData2, stream, workerOptions, onTaskFinished);
    } else {
      return new Promise((resolve) => pendingRequests.push({ resolve, stream, workerOptions }));
    }
  }
  function onTaskFinished(workerData) {
    if (pendingRequests.length) {
      const [{ resolve, stream: stream2, workerOptions: workerOptions2 }] = pendingRequests.splice(0, 1);
      resolve(new CodecWorker(workerData, stream2, workerOptions2, onTaskFinished));
    } else if (workerData.worker) {
      clearTerminateTimeout(workerData);
      terminateWorker(workerData, workerOptions);
    } else {
      pool = pool.filter((data) => data != workerData);
    }
  }
}
function terminateWorker(workerData, workerOptions) {
  const { config: config2 } = workerOptions;
  const { terminateWorkerTimeout } = config2;
  if (Number.isFinite(terminateWorkerTimeout) && terminateWorkerTimeout >= 0) {
    if (workerData.terminated) {
      workerData.terminated = false;
    } else {
      workerData.terminateTimeout = setTimeout(async () => {
        pool = pool.filter((data) => data != workerData);
        try {
          await workerData.terminate();
        } catch (_) {
        }
      }, terminateWorkerTimeout);
    }
  }
}
function clearTerminateTimeout(workerData) {
  const { terminateTimeout } = workerData;
  if (terminateTimeout) {
    clearTimeout(terminateTimeout);
    workerData.terminateTimeout = null;
  }
}

// node_modules/@zip.js/zip.js/lib/z-worker-inline.js
function e(e2, t = {}) {
  const n = 'const{Array:e,Object:t,Number:n,Math:r,Error:s,Uint8Array:i,Uint16Array:o,Uint32Array:c,Int32Array:f,Map:a,DataView:l,Promise:u,TextEncoder:w,crypto:h,postMessage:d,TransformStream:p,ReadableStream:y,WritableStream:m,CompressionStream:b,DecompressionStream:g}=self,k=void 0,v="undefined",S="function";class z{constructor(e){return class extends p{constructor(t,n){const r=new e(n);super({transform(e,t){t.enqueue(r.append(e))},flush(e){const t=r.flush();t&&e.enqueue(t)}})}}}}const C=[];for(let e=0;256>e;e++){let t=e;for(let e=0;8>e;e++)1&t?t=t>>>1^3988292384:t>>>=1;C[e]=t}class x{constructor(e){this.t=e||-1}append(e){let t=0|this.t;for(let n=0,r=0|e.length;r>n;n++)t=t>>>8^C[255&(t^e[n])];this.t=t}get(){return~this.t}}class A extends p{constructor(){let e;const t=new x;super({transform(e,n){t.append(e),n.enqueue(e)},flush(){const n=new i(4);new l(n.buffer).setUint32(0,t.get()),e.value=n}}),e=this}}const _={concat(e,t){if(0===e.length||0===t.length)return e.concat(t);const n=e[e.length-1],r=_.i(n);return 32===r?e.concat(t):_.o(t,r,0|n,e.slice(0,e.length-1))},l(e){const t=e.length;if(0===t)return 0;const n=e[t-1];return 32*(t-1)+_.i(n)},u(e,t){if(32*e.length<t)return e;const n=(e=e.slice(0,r.ceil(t/32))).length;return t&=31,n>0&&t&&(e[n-1]=_.h(t,e[n-1]&2147483648>>t-1,1)),e},h:(e,t,n)=>32===e?t:(n?0|t:t<<32-e)+1099511627776*e,i:e=>r.round(e/1099511627776)||32,o(e,t,n,r){for(void 0===r&&(r=[]);t>=32;t-=32)r.push(n),n=0;if(0===t)return r.concat(e);for(let s=0;s<e.length;s++)r.push(n|e[s]>>>t),n=e[s]<<32-t;const s=e.length?e[e.length-1]:0,i=_.i(s);return r.push(_.h(t+i&31,t+i>32?n:r.pop(),1)),r}},I={bytes:{p(e){const t=_.l(e)/8,n=new i(t);let r;for(let s=0;t>s;s++)3&s||(r=e[s/4]),n[s]=r>>>24,r<<=8;return n},m(e){const t=[];let n,r=0;for(n=0;n<e.length;n++)r=r<<8|e[n],3&~n||(t.push(r),r=0);return 3&n&&t.push(_.h(8*(3&n),r)),t}}},P=class{constructor(e){const t=this;t.blockSize=512,t.k=[1732584193,4023233417,2562383102,271733878,3285377520],t.v=[1518500249,1859775393,2400959708,3395469782],e?(t.S=e.S.slice(0),t.C=e.C.slice(0),t.A=e.A):t.reset()}reset(){const e=this;return e.S=e.k.slice(0),e.C=[],e.A=0,e}update(e){const t=this;"string"==typeof e&&(e=I._.m(e));const n=t.C=_.concat(t.C,e),r=t.A,i=t.A=r+_.l(e);if(i>9007199254740991)throw new s("Cannot hash more than 2^53 - 1 bits");const o=new c(n);let f=0;for(let e=t.blockSize+r-(t.blockSize+r&t.blockSize-1);i>=e;e+=t.blockSize)t.I(o.subarray(16*f,16*(f+1))),f+=1;return n.splice(0,16*f),t}P(){const e=this;let t=e.C;const n=e.S;t=_.concat(t,[_.h(1,1)]);for(let e=t.length+2;15&e;e++)t.push(0);for(t.push(r.floor(e.A/4294967296)),t.push(0|e.A);t.length;)e.I(t.splice(0,16));return e.reset(),n}D(e,t,n,r){return e>19?e>39?e>59?e>79?void 0:t^n^r:t&n|t&r|n&r:t^n^r:t&n|~t&r}V(e,t){return t<<e|t>>>32-e}I(t){const n=this,s=n.S,i=e(80);for(let e=0;16>e;e++)i[e]=t[e];let o=s[0],c=s[1],f=s[2],a=s[3],l=s[4];for(let e=0;79>=e;e++){16>e||(i[e]=n.V(1,i[e-3]^i[e-8]^i[e-14]^i[e-16]));const t=n.V(5,o)+n.D(e,c,f,a)+l+i[e]+n.v[r.floor(e/20)]|0;l=a,a=f,f=n.V(30,c),c=o,o=t}s[0]=s[0]+o|0,s[1]=s[1]+c|0,s[2]=s[2]+f|0,s[3]=s[3]+a|0,s[4]=s[4]+l|0}},D={getRandomValues(e){const t=new c(e.buffer),n=e=>{let t=987654321;const n=4294967295;return()=>(t=36969*(65535&t)+(t>>16)&n,(((t<<16)+(e=18e3*(65535&e)+(e>>16)&n)&n)/4294967296+.5)*(r.random()>.5?1:-1))};for(let s,i=0;i<e.length;i+=4){const e=n(4294967296*(s||r.random()));s=987654071*e(),t[i/4]=4294967296*e()|0}return e}},V={importKey:e=>new V.R(I.bytes.m(e)),B(e,t,n,r){if(n=n||1e4,0>r||0>n)throw new s("invalid params to pbkdf2");const i=1+(r>>5)<<2;let o,c,f,a,u;const w=new ArrayBuffer(i),h=new l(w);let d=0;const p=_;for(t=I.bytes.m(t),u=1;(i||1)>d;u++){for(o=c=e.encrypt(p.concat(t,[u])),f=1;n>f;f++)for(c=e.encrypt(c),a=0;a<c.length;a++)o[a]^=c[a];for(f=0;(i||1)>d&&f<o.length;f++)h.setInt32(d,o[f]),d+=4}return w.slice(0,r/8)},R:class{constructor(e){const t=this,n=t.M=P,r=[[],[]];t.U=[new n,new n];const s=t.U[0].blockSize/32;e.length>s&&(e=(new n).update(e).P());for(let t=0;s>t;t++)r[0][t]=909522486^e[t],r[1][t]=1549556828^e[t];t.U[0].update(r[0]),t.U[1].update(r[1]),t.K=new n(t.U[0])}reset(){const e=this;e.K=new e.M(e.U[0]),e.N=!1}update(e){this.N=!0,this.K.update(e)}digest(){const e=this,t=e.K.P(),n=new e.M(e.U[1]).update(t).P();return e.reset(),n}encrypt(e){if(this.N)throw new s("encrypt on already updated hmac called!");return this.update(e),this.digest(e)}}},R=typeof h!=v&&typeof h.getRandomValues==S,B="Invalid password",E="Invalid signature",M="zipjs-abort-check-password";function U(e){return R?h.getRandomValues(e):D.getRandomValues(e)}const K=16,N={name:"PBKDF2"},O=t.assign({hash:{name:"HMAC"}},N),T=t.assign({iterations:1e3,hash:{name:"SHA-1"}},N),W=["deriveBits"],j=[8,12,16],H=[16,24,32],L=10,F=[0,0,0,0],q=typeof h!=v,G=q&&h.subtle,J=q&&typeof G!=v,Q=I.bytes,X=class{constructor(e){const t=this;t.O=[[[],[],[],[],[]],[[],[],[],[],[]]],t.O[0][0][0]||t.T();const n=t.O[0][4],r=t.O[1],i=e.length;let o,c,f,a=1;if(4!==i&&6!==i&&8!==i)throw new s("invalid aes key size");for(t.v=[c=e.slice(0),f=[]],o=i;4*i+28>o;o++){let e=c[o-1];(o%i==0||8===i&&o%i==4)&&(e=n[e>>>24]<<24^n[e>>16&255]<<16^n[e>>8&255]<<8^n[255&e],o%i==0&&(e=e<<8^e>>>24^a<<24,a=a<<1^283*(a>>7))),c[o]=c[o-i]^e}for(let e=0;o;e++,o--){const t=c[3&e?o:o-4];f[e]=4>=o||4>e?t:r[0][n[t>>>24]]^r[1][n[t>>16&255]]^r[2][n[t>>8&255]]^r[3][n[255&t]]}}encrypt(e){return this.W(e,0)}decrypt(e){return this.W(e,1)}T(){const e=this.O[0],t=this.O[1],n=e[4],r=t[4],s=[],i=[];let o,c,f,a;for(let e=0;256>e;e++)i[(s[e]=e<<1^283*(e>>7))^e]=e;for(let l=o=0;!n[l];l^=c||1,o=i[o]||1){let i=o^o<<1^o<<2^o<<3^o<<4;i=i>>8^255&i^99,n[l]=i,r[i]=l,a=s[f=s[c=s[l]]];let u=16843009*a^65537*f^257*c^16843008*l,w=257*s[i]^16843008*i;for(let n=0;4>n;n++)e[n][l]=w=w<<24^w>>>8,t[n][i]=u=u<<24^u>>>8}for(let n=0;5>n;n++)e[n]=e[n].slice(0),t[n]=t[n].slice(0)}W(e,t){if(4!==e.length)throw new s("invalid aes block size");const n=this.v[t],r=n.length/4-2,i=[0,0,0,0],o=this.O[t],c=o[0],f=o[1],a=o[2],l=o[3],u=o[4];let w,h,d,p=e[0]^n[0],y=e[t?3:1]^n[1],m=e[2]^n[2],b=e[t?1:3]^n[3],g=4;for(let e=0;r>e;e++)w=c[p>>>24]^f[y>>16&255]^a[m>>8&255]^l[255&b]^n[g],h=c[y>>>24]^f[m>>16&255]^a[b>>8&255]^l[255&p]^n[g+1],d=c[m>>>24]^f[b>>16&255]^a[p>>8&255]^l[255&y]^n[g+2],b=c[b>>>24]^f[p>>16&255]^a[y>>8&255]^l[255&m]^n[g+3],g+=4,p=w,y=h,m=d;for(let e=0;4>e;e++)i[t?3&-e:e]=u[p>>>24]<<24^u[y>>16&255]<<16^u[m>>8&255]<<8^u[255&b]^n[g++],w=p,p=y,y=m,m=b,b=w;return i}},Y=class{constructor(e,t){this.j=e,this.H=t,this.L=t}reset(){this.L=this.H}update(e){return this.F(this.j,e,this.L)}q(e){if(255&~(e>>24))e+=1<<24;else{let t=e>>16&255,n=e>>8&255,r=255&e;255===t?(t=0,255===n?(n=0,255===r?r=0:++r):++n):++t,e=0,e+=t<<16,e+=n<<8,e+=r}return e}G(e){0===(e[0]=this.q(e[0]))&&(e[1]=this.q(e[1]))}F(e,t,n){let r;if(!(r=t.length))return[];const s=_.l(t);for(let s=0;r>s;s+=4){this.G(n);const r=e.encrypt(n);t[s]^=r[0],t[s+1]^=r[1],t[s+2]^=r[2],t[s+3]^=r[3]}return _.u(t,s)}},Z=V.R;let $=q&&J&&typeof G.importKey==S,ee=q&&J&&typeof G.deriveBits==S;class te extends p{constructor({password:e,rawPassword:n,signed:r,encryptionStrength:o,checkPasswordOnly:c}){super({start(){t.assign(this,{ready:new u((e=>this.J=e)),password:ie(e,n),signed:r,X:o-1,pending:new i})},async transform(e,t){const n=this,{password:r,X:o,J:f,ready:a}=n;r?(await(async(e,t,n,r)=>{const i=await se(e,t,n,ce(r,0,j[t])),o=ce(r,j[t]);if(i[0]!=o[0]||i[1]!=o[1])throw new s(B)})(n,o,r,ce(e,0,j[o]+2)),e=ce(e,j[o]+2),c?t.error(new s(M)):f()):await a;const l=new i(e.length-L-(e.length-L)%K);t.enqueue(re(n,e,l,0,L,!0))},async flush(e){const{signed:t,Y:n,Z:r,pending:o,ready:c}=this;if(r&&n){await c;const f=ce(o,0,o.length-L),a=ce(o,o.length-L);let l=new i;if(f.length){const e=ae(Q,f);r.update(e);const t=n.update(e);l=fe(Q,t)}if(t){const e=ce(fe(Q,r.digest()),0,L);for(let t=0;L>t;t++)if(e[t]!=a[t])throw new s(E)}e.enqueue(l)}}})}}class ne extends p{constructor({password:e,rawPassword:n,encryptionStrength:r}){let s;super({start(){t.assign(this,{ready:new u((e=>this.J=e)),password:ie(e,n),X:r-1,pending:new i})},async transform(e,t){const n=this,{password:r,X:s,J:o,ready:c}=n;let f=new i;r?(f=await(async(e,t,n)=>{const r=U(new i(j[t]));return oe(r,await se(e,t,n,r))})(n,s,r),o()):await c;const a=new i(f.length+e.length-e.length%K);a.set(f,0),t.enqueue(re(n,e,a,f.length,0))},async flush(e){const{Y:t,Z:n,pending:r,ready:o}=this;if(n&&t){await o;let c=new i;if(r.length){const e=t.update(ae(Q,r));n.update(e),c=fe(Q,e)}s.signature=fe(Q,n.digest()).slice(0,L),e.enqueue(oe(c,s.signature))}}}),s=this}}function re(e,t,n,r,s,o){const{Y:c,Z:f,pending:a}=e,l=t.length-s;let u;for(a.length&&(t=oe(a,t),n=((e,t)=>{if(t&&t>e.length){const n=e;(e=new i(t)).set(n,0)}return e})(n,l-l%K)),u=0;l-K>=u;u+=K){const e=ae(Q,ce(t,u,u+K));o&&f.update(e);const s=c.update(e);o||f.update(s),n.set(fe(Q,s),u+r)}return e.pending=ce(t,u),n}async function se(n,r,s,o){n.password=null;const c=await(async(e,t,n,r,s)=>{if(!$)return V.importKey(t);try{return await G.importKey("raw",t,n,!1,s)}catch(e){return $=!1,V.importKey(t)}})(0,s,O,0,W),f=await(async(e,t,n)=>{if(!ee)return V.B(t,e.salt,T.iterations,n);try{return await G.deriveBits(e,t,n)}catch(r){return ee=!1,V.B(t,e.salt,T.iterations,n)}})(t.assign({salt:o},T),c,8*(2*H[r]+2)),a=new i(f),l=ae(Q,ce(a,0,H[r])),u=ae(Q,ce(a,H[r],2*H[r])),w=ce(a,2*H[r]);return t.assign(n,{keys:{key:l,$:u,passwordVerification:w},Y:new Y(new X(l),e.from(F)),Z:new Z(u)}),w}function ie(e,t){return t===k?(e=>{if(typeof w==v){const t=new i((e=unescape(encodeURIComponent(e))).length);for(let n=0;n<t.length;n++)t[n]=e.charCodeAt(n);return t}return(new w).encode(e)})(e):t}function oe(e,t){let n=e;return e.length+t.length&&(n=new i(e.length+t.length),n.set(e,0),n.set(t,e.length)),n}function ce(e,t,n){return e.subarray(t,n)}function fe(e,t){return e.p(t)}function ae(e,t){return e.m(t)}class le extends p{constructor({password:e,passwordVerification:n,checkPasswordOnly:r}){super({start(){t.assign(this,{password:e,passwordVerification:n}),de(this,e)},transform(e,t){const n=this;if(n.password){const t=we(n,e.subarray(0,12));if(n.password=null,t[11]!=n.passwordVerification)throw new s(B);e=e.subarray(12)}r?t.error(new s(M)):t.enqueue(we(n,e))}})}}class ue extends p{constructor({password:e,passwordVerification:n}){super({start(){t.assign(this,{password:e,passwordVerification:n}),de(this,e)},transform(e,t){const n=this;let r,s;if(n.password){n.password=null;const t=U(new i(12));t[11]=n.passwordVerification,r=new i(e.length+t.length),r.set(he(n,t),0),s=12}else r=new i(e.length),s=0;r.set(he(n,e),s),t.enqueue(r)}})}}function we(e,t){const n=new i(t.length);for(let r=0;r<t.length;r++)n[r]=ye(e)^t[r],pe(e,n[r]);return n}function he(e,t){const n=new i(t.length);for(let r=0;r<t.length;r++)n[r]=ye(e)^t[r],pe(e,t[r]);return n}function de(e,n){const r=[305419896,591751049,878082192];t.assign(e,{keys:r,ee:new x(r[0]),te:new x(r[2])});for(let t=0;t<n.length;t++)pe(e,n.charCodeAt(t))}function pe(e,t){let[n,s,i]=e.keys;e.ee.append([t]),n=~e.ee.get(),s=be(r.imul(be(s+me(n)),134775813)+1),e.te.append([s>>>24]),i=~e.te.get(),e.keys=[n,s,i]}function ye(e){const t=2|e.keys[2];return me(r.imul(t,1^t)>>>8)}function me(e){return 255&e}function be(e){return 4294967295&e}const ge="deflate-raw";class ke extends p{constructor(e,{chunkSize:t,CompressionStream:n,CompressionStreamNative:r}){super({});const{compressed:s,encrypted:i,useCompressionStream:o,zipCrypto:c,signed:f,level:a}=e,u=this;let w,h,d=Se(super.readable);i&&!c||!f||(w=new A,d=xe(d,w)),s&&(d=Ce(d,o,{level:a,chunkSize:t},r,n)),i&&(c?d=xe(d,new ue(e)):(h=new ne(e),d=xe(d,h))),ze(u,d,(()=>{let e;i&&!c&&(e=h.signature),i&&!c||!f||(e=new l(w.value.buffer).getUint32(0)),u.signature=e}))}}class ve extends p{constructor(e,{chunkSize:t,DecompressionStream:n,DecompressionStreamNative:r}){super({});const{zipCrypto:i,encrypted:o,signed:c,signature:f,compressed:a,useCompressionStream:u}=e;let w,h,d=Se(super.readable);o&&(i?d=xe(d,new le(e)):(h=new te(e),d=xe(d,h))),a&&(d=Ce(d,u,{chunkSize:t},r,n)),o&&!i||!c||(w=new A,d=xe(d,w)),ze(this,d,(()=>{if((!o||i)&&c){const e=new l(w.value.buffer);if(f!=e.getUint32(0,!1))throw new s(E)}}))}}function Se(e){return xe(e,new p({transform(e,t){e&&e.length&&t.enqueue(e)}}))}function ze(e,n,r){n=xe(n,new p({flush:r})),t.defineProperty(e,"readable",{get:()=>n})}function Ce(e,t,n,r,s){try{e=xe(e,new(t&&r?r:s)(ge,n))}catch(r){if(!t)return e;try{e=xe(e,new s(ge,n))}catch(t){return e}}return e}function xe(e,t){return e.pipeThrough(t)}const Ae="data",_e="close";class Ie extends p{constructor(e,n){super({});const r=this,{codecType:s}=e;let i;s.startsWith("deflate")?i=ke:s.startsWith("inflate")&&(i=ve);let o=0,c=0;const f=new i(e,n),a=super.readable,l=new p({transform(e,t){e&&e.length&&(c+=e.length,t.enqueue(e))},flush(){t.assign(r,{inputSize:c})}}),u=new p({transform(e,t){e&&e.length&&(o+=e.length,t.enqueue(e))},flush(){const{signature:e}=f;t.assign(r,{signature:e,outputSize:o,inputSize:c})}});t.defineProperty(r,"readable",{get:()=>a.pipeThrough(l).pipeThrough(f).pipeThrough(u)})}}class Pe extends p{constructor(e){let t;super({transform:function n(r,s){if(t){const e=new i(t.length+r.length);e.set(t),e.set(r,t.length),r=e,t=null}r.length>e?(s.enqueue(r.slice(0,e)),n(r.slice(e),s)):t=r},flush(e){t&&t.length&&e.enqueue(t)}})}}const De=new a,Ve=new a;let Re,Be=0,Ee=!0;async function Me(e){try{const{options:t,scripts:r,config:s}=e;if(r&&r.length)try{Ee?importScripts.apply(k,r):await Ue(r)}catch(e){Ee=!1,await Ue(r)}self.initCodec&&self.initCodec(),s.CompressionStreamNative=self.CompressionStream,s.DecompressionStreamNative=self.DecompressionStream,self.Deflate&&(s.CompressionStream=new z(self.Deflate)),self.Inflate&&(s.DecompressionStream=new z(self.Inflate));const i={highWaterMark:1},o=e.readable||new y({async pull(e){const t=new u((e=>De.set(Be,e)));Ke({type:"pull",messageId:Be}),Be=(Be+1)%n.MAX_SAFE_INTEGER;const{value:r,done:s}=await t;e.enqueue(r),s&&e.close()}},i),c=e.writable||new m({async write(e){let t;const r=new u((e=>t=e));Ve.set(Be,t),Ke({type:Ae,value:e,messageId:Be}),Be=(Be+1)%n.MAX_SAFE_INTEGER,await r}},i),f=new Ie(t,s);Re=new AbortController;const{signal:a}=Re;await o.pipeThrough(f).pipeThrough(new Pe(s.chunkSize)).pipeTo(c,{signal:a,preventClose:!0,preventAbort:!0}),await c.getWriter().close();const{signature:l,inputSize:w,outputSize:h}=f;Ke({type:_e,result:{signature:l,inputSize:w,outputSize:h}})}catch(e){Ne(e)}}async function Ue(e){for(const t of e)await import(t)}function Ke(e){let{value:t}=e;if(t)if(t.length)try{t=new i(t),e.value=t.buffer,d(e,[e.value])}catch(t){d(e)}else d(e);else d(e)}function Ne(e=new s("Unknown error")){const{message:t,stack:n,code:r,name:i}=e;d({error:{message:t,stack:n,code:r,name:i}})}addEventListener("message",(({data:e})=>{const{type:t,messageId:n,value:r,done:s}=e;try{if("start"==t&&Me(e),t==Ae){const e=De.get(n);De.delete(n),e({value:new i(r),done:s})}if("ack"==t){const e=Ve.get(n);Ve.delete(n),e()}t==_e&&Re.abort()}catch(e){Ne(e)}}));const Oe=-2;function Te(t){return We(t.map((([t,n])=>new e(t).fill(n,0,t))))}function We(t){return t.reduce(((t,n)=>t.concat(e.isArray(n)?We(n):n)),[])}const je=[0,1,2,3].concat(...Te([[2,4],[2,5],[4,6],[4,7],[8,8],[8,9],[16,10],[16,11],[32,12],[32,13],[64,14],[64,15],[2,0],[1,16],[1,17],[2,18],[2,19],[4,20],[4,21],[8,22],[8,23],[16,24],[16,25],[32,26],[32,27],[64,28],[64,29]]));function He(){const e=this;function t(e,t){let n=0;do{n|=1&e,e>>>=1,n<<=1}while(--t>0);return n>>>1}e.ne=n=>{const s=e.re,i=e.ie.se,o=e.ie.oe;let c,f,a,l=-1;for(n.ce=0,n.fe=573,c=0;o>c;c++)0!==s[2*c]?(n.ae[++n.ce]=l=c,n.le[c]=0):s[2*c+1]=0;for(;2>n.ce;)a=n.ae[++n.ce]=2>l?++l:0,s[2*a]=1,n.le[a]=0,n.ue--,i&&(n.we-=i[2*a+1]);for(e.he=l,c=r.floor(n.ce/2);c>=1;c--)n.de(s,c);a=o;do{c=n.ae[1],n.ae[1]=n.ae[n.ce--],n.de(s,1),f=n.ae[1],n.ae[--n.fe]=c,n.ae[--n.fe]=f,s[2*a]=s[2*c]+s[2*f],n.le[a]=r.max(n.le[c],n.le[f])+1,s[2*c+1]=s[2*f+1]=a,n.ae[1]=a++,n.de(s,1)}while(n.ce>=2);n.ae[--n.fe]=n.ae[1],(t=>{const n=e.re,r=e.ie.se,s=e.ie.pe,i=e.ie.ye,o=e.ie.me;let c,f,a,l,u,w,h=0;for(l=0;15>=l;l++)t.be[l]=0;for(n[2*t.ae[t.fe]+1]=0,c=t.fe+1;573>c;c++)f=t.ae[c],l=n[2*n[2*f+1]+1]+1,l>o&&(l=o,h++),n[2*f+1]=l,f>e.he||(t.be[l]++,u=0,i>f||(u=s[f-i]),w=n[2*f],t.ue+=w*(l+u),r&&(t.we+=w*(r[2*f+1]+u)));if(0!==h){do{for(l=o-1;0===t.be[l];)l--;t.be[l]--,t.be[l+1]+=2,t.be[o]--,h-=2}while(h>0);for(l=o;0!==l;l--)for(f=t.be[l];0!==f;)a=t.ae[--c],a>e.he||(n[2*a+1]!=l&&(t.ue+=(l-n[2*a+1])*n[2*a],n[2*a+1]=l),f--)}})(n),((e,n,r)=>{const s=[];let i,o,c,f=0;for(i=1;15>=i;i++)s[i]=f=f+r[i-1]<<1;for(o=0;n>=o;o++)c=e[2*o+1],0!==c&&(e[2*o]=t(s[c]++,c))})(s,e.he,n.be)}}function Le(e,t,n,r,s){const i=this;i.se=e,i.pe=t,i.ye=n,i.oe=r,i.me=s}He.ge=[0,1,2,3,4,5,6,7].concat(...Te([[2,8],[2,9],[2,10],[2,11],[4,12],[4,13],[4,14],[4,15],[8,16],[8,17],[8,18],[8,19],[16,20],[16,21],[16,22],[16,23],[32,24],[32,25],[32,26],[31,27],[1,28]])),He.ke=[0,1,2,3,4,5,6,7,8,10,12,14,16,20,24,28,32,40,48,56,64,80,96,112,128,160,192,224,0],He.ve=[0,1,2,3,4,6,8,12,16,24,32,48,64,96,128,192,256,384,512,768,1024,1536,2048,3072,4096,6144,8192,12288,16384,24576],He.Se=e=>256>e?je[e]:je[256+(e>>>7)],He.ze=[0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0],He.Ce=[0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13],He.xe=[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,3,7],He.Ae=[16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15];const Fe=Te([[144,8],[112,9],[24,7],[8,8]]);Le._e=We([12,140,76,204,44,172,108,236,28,156,92,220,60,188,124,252,2,130,66,194,34,162,98,226,18,146,82,210,50,178,114,242,10,138,74,202,42,170,106,234,26,154,90,218,58,186,122,250,6,134,70,198,38,166,102,230,22,150,86,214,54,182,118,246,14,142,78,206,46,174,110,238,30,158,94,222,62,190,126,254,1,129,65,193,33,161,97,225,17,145,81,209,49,177,113,241,9,137,73,201,41,169,105,233,25,153,89,217,57,185,121,249,5,133,69,197,37,165,101,229,21,149,85,213,53,181,117,245,13,141,77,205,45,173,109,237,29,157,93,221,61,189,125,253,19,275,147,403,83,339,211,467,51,307,179,435,115,371,243,499,11,267,139,395,75,331,203,459,43,299,171,427,107,363,235,491,27,283,155,411,91,347,219,475,59,315,187,443,123,379,251,507,7,263,135,391,71,327,199,455,39,295,167,423,103,359,231,487,23,279,151,407,87,343,215,471,55,311,183,439,119,375,247,503,15,271,143,399,79,335,207,463,47,303,175,431,111,367,239,495,31,287,159,415,95,351,223,479,63,319,191,447,127,383,255,511,0,64,32,96,16,80,48,112,8,72,40,104,24,88,56,120,4,68,36,100,20,84,52,116,3,131,67,195,35,163,99,227].map(((e,t)=>[e,Fe[t]])));const qe=Te([[30,5]]);function Ge(e,t,n,r,s){const i=this;i.Ie=e,i.Pe=t,i.De=n,i.Ve=r,i.Re=s}Le.Be=We([0,16,8,24,4,20,12,28,2,18,10,26,6,22,14,30,1,17,9,25,5,21,13,29,3,19,11,27,7,23].map(((e,t)=>[e,qe[t]]))),Le.Ee=new Le(Le._e,He.ze,257,286,15),Le.Me=new Le(Le.Be,He.Ce,0,30,15),Le.Ue=new Le(null,He.xe,0,19,7);const Je=[new Ge(0,0,0,0,0),new Ge(4,4,8,4,1),new Ge(4,5,16,8,1),new Ge(4,6,32,32,1),new Ge(4,4,16,16,2),new Ge(8,16,32,32,2),new Ge(8,16,128,128,2),new Ge(8,32,128,256,2),new Ge(32,128,258,1024,2),new Ge(32,258,258,4096,2)],Qe=["need dictionary","stream end","","","stream error","data error","","buffer error","",""],Xe=113,Ye=666,Ze=262;function $e(e,t,n,r){const s=e[2*t],i=e[2*n];return i>s||s==i&&r[t]<=r[n]}function et(){const e=this;let t,n,s,c,f,a,l,u,w,h,d,p,y,m,b,g,k,v,S,z,C,x,A,_,I,P,D,V,R,B,E,M,U;const K=new He,N=new He,O=new He;let T,W,j,H,L,F;function q(){let t;for(t=0;286>t;t++)E[2*t]=0;for(t=0;30>t;t++)M[2*t]=0;for(t=0;19>t;t++)U[2*t]=0;E[512]=1,e.ue=e.we=0,W=j=0}function G(e,t){let n,r=-1,s=e[1],i=0,o=7,c=4;0===s&&(o=138,c=3),e[2*(t+1)+1]=65535;for(let f=0;t>=f;f++)n=s,s=e[2*(f+1)+1],++i<o&&n==s||(c>i?U[2*n]+=i:0!==n?(n!=r&&U[2*n]++,U[32]++):i>10?U[36]++:U[34]++,i=0,r=n,0===s?(o=138,c=3):n==s?(o=6,c=3):(o=7,c=4))}function J(t){e.Ke[e.pending++]=t}function Q(e){J(255&e),J(e>>>8&255)}function X(e,t){let n;const r=t;F>16-r?(n=e,L|=n<<F&65535,Q(L),L=n>>>16-F,F+=r-16):(L|=e<<F&65535,F+=r)}function Y(e,t){const n=2*e;X(65535&t[n],65535&t[n+1])}function Z(e,t){let n,r,s=-1,i=e[1],o=0,c=7,f=4;for(0===i&&(c=138,f=3),n=0;t>=n;n++)if(r=i,i=e[2*(n+1)+1],++o>=c||r!=i){if(f>o)do{Y(r,U)}while(0!=--o);else 0!==r?(r!=s&&(Y(r,U),o--),Y(16,U),X(o-3,2)):o>10?(Y(18,U),X(o-11,7)):(Y(17,U),X(o-3,3));o=0,s=r,0===i?(c=138,f=3):r==i?(c=6,f=3):(c=7,f=4)}}function $(){16==F?(Q(L),L=0,F=0):8>F||(J(255&L),L>>>=8,F-=8)}function ee(t,n){let s,i,o;if(e.Ne[W]=t,e.Oe[W]=255&n,W++,0===t?E[2*n]++:(j++,t--,E[2*(He.ge[n]+256+1)]++,M[2*He.Se(t)]++),!(8191&W)&&D>2){for(s=8*W,i=C-k,o=0;30>o;o++)s+=M[2*o]*(5+He.Ce[o]);if(s>>>=3,j<r.floor(W/2)&&s<r.floor(i/2))return!0}return W==T-1}function te(t,n){let r,s,i,o,c=0;if(0!==W)do{r=e.Ne[c],s=e.Oe[c],c++,0===r?Y(s,t):(i=He.ge[s],Y(i+256+1,t),o=He.ze[i],0!==o&&(s-=He.ke[i],X(s,o)),r--,i=He.Se(r),Y(i,n),o=He.Ce[i],0!==o&&(r-=He.ve[i],X(r,o)))}while(W>c);Y(256,t),H=t[513]}function ne(){F>8?Q(L):F>0&&J(255&L),L=0,F=0}function re(t,n,r){X(0+(r?1:0),3),((t,n)=>{ne(),H=8,Q(n),Q(~n),e.Ke.set(u.subarray(t,t+n),e.pending),e.pending+=n})(t,n)}function se(n){((t,n,r)=>{let s,i,o=0;D>0?(K.ne(e),N.ne(e),o=(()=>{let t;for(G(E,K.he),G(M,N.he),O.ne(e),t=18;t>=3&&0===U[2*He.Ae[t]+1];t--);return e.ue+=14+3*(t+1),t})(),s=e.ue+3+7>>>3,i=e.we+3+7>>>3,i>s||(s=i)):s=i=n+5,n+4>s||-1==t?i==s?(X(2+(r?1:0),3),te(Le._e,Le.Be)):(X(4+(r?1:0),3),((e,t,n)=>{let r;for(X(e-257,5),X(t-1,5),X(n-4,4),r=0;n>r;r++)X(U[2*He.Ae[r]+1],3);Z(E,e-1),Z(M,t-1)})(K.he+1,N.he+1,o+1),te(E,M)):re(t,n,r),q(),r&&ne()})(0>k?-1:k,C-k,n),k=C,t.Te()}function ie(){let e,n,r,s;do{if(s=w-A-C,0===s&&0===C&&0===A)s=f;else if(-1==s)s--;else if(C>=f+f-Ze){u.set(u.subarray(f,f+f),0),x-=f,C-=f,k-=f,e=y,r=e;do{n=65535&d[--r],d[r]=f>n?0:n-f}while(0!=--e);e=f,r=e;do{n=65535&h[--r],h[r]=f>n?0:n-f}while(0!=--e);s+=f}if(0===t.We)return;e=t.je(u,C+A,s),A+=e,3>A||(p=255&u[C],p=(p<<g^255&u[C+1])&b)}while(Ze>A&&0!==t.We)}function oe(e){let t,n,r=I,s=C,i=_;const o=C>f-Ze?C-(f-Ze):0;let c=B;const a=l,w=C+258;let d=u[s+i-1],p=u[s+i];R>_||(r>>=2),c>A&&(c=A);do{if(t=e,u[t+i]==p&&u[t+i-1]==d&&u[t]==u[s]&&u[++t]==u[s+1]){s+=2,t++;do{}while(u[++s]==u[++t]&&u[++s]==u[++t]&&u[++s]==u[++t]&&u[++s]==u[++t]&&u[++s]==u[++t]&&u[++s]==u[++t]&&u[++s]==u[++t]&&u[++s]==u[++t]&&w>s);if(n=258-(w-s),s=w-258,n>i){if(x=e,i=n,n>=c)break;d=u[s+i-1],p=u[s+i]}}}while((e=65535&h[e&a])>o&&0!=--r);return i>A?A:i}e.le=[],e.be=[],e.ae=[],E=[],M=[],U=[],e.de=(t,n)=>{const r=e.ae,s=r[n];let i=n<<1;for(;i<=e.ce&&(i<e.ce&&$e(t,r[i+1],r[i],e.le)&&i++,!$e(t,s,r[i],e.le));)r[n]=r[i],n=i,i<<=1;r[n]=s},e.He=(t,S,x,W,j,G)=>(W||(W=8),j||(j=8),G||(G=0),t.Le=null,-1==S&&(S=6),1>j||j>9||8!=W||9>x||x>15||0>S||S>9||0>G||G>2?Oe:(t.Fe=e,a=x,f=1<<a,l=f-1,m=j+7,y=1<<m,b=y-1,g=r.floor((m+3-1)/3),u=new i(2*f),h=[],d=[],T=1<<j+6,e.Ke=new i(4*T),s=4*T,e.Ne=new o(T),e.Oe=new i(T),D=S,V=G,(t=>(t.qe=t.Ge=0,t.Le=null,e.pending=0,e.Je=0,n=Xe,c=0,K.re=E,K.ie=Le.Ee,N.re=M,N.ie=Le.Me,O.re=U,O.ie=Le.Ue,L=0,F=0,H=8,q(),(()=>{w=2*f,d[y-1]=0;for(let e=0;y-1>e;e++)d[e]=0;P=Je[D].Pe,R=Je[D].Ie,B=Je[D].De,I=Je[D].Ve,C=0,k=0,A=0,v=_=2,z=0,p=0})(),0))(t))),e.Qe=()=>42!=n&&n!=Xe&&n!=Ye?Oe:(e.Oe=null,e.Ne=null,e.Ke=null,d=null,h=null,u=null,e.Fe=null,n==Xe?-3:0),e.Xe=(e,t,n)=>{let r=0;return-1==t&&(t=6),0>t||t>9||0>n||n>2?Oe:(Je[D].Re!=Je[t].Re&&0!==e.qe&&(r=e.Ye(1)),D!=t&&(D=t,P=Je[D].Pe,R=Je[D].Ie,B=Je[D].De,I=Je[D].Ve),V=n,r)},e.Ze=(e,t,r)=>{let s,i=r,o=0;if(!t||42!=n)return Oe;if(3>i)return 0;for(i>f-Ze&&(i=f-Ze,o=r-i),u.set(t.subarray(o,o+i),0),C=i,k=i,p=255&u[0],p=(p<<g^255&u[1])&b,s=0;i-3>=s;s++)p=(p<<g^255&u[s+2])&b,h[s&l]=d[p],d[p]=s;return 0},e.Ye=(r,i)=>{let o,w,m,I,R;if(i>4||0>i)return Oe;if(!r.$e||!r.et&&0!==r.We||n==Ye&&4!=i)return r.Le=Qe[4],Oe;if(0===r.tt)return r.Le=Qe[7],-5;var B;if(t=r,I=c,c=i,42==n&&(w=8+(a-8<<4)<<8,m=(D-1&255)>>1,m>3&&(m=3),w|=m<<6,0!==C&&(w|=32),w+=31-w%31,n=Xe,J((B=w)>>8&255),J(255&B)),0!==e.pending){if(t.Te(),0===t.tt)return c=-1,0}else if(0===t.We&&I>=i&&4!=i)return t.Le=Qe[7],-5;if(n==Ye&&0!==t.We)return r.Le=Qe[7],-5;if(0!==t.We||0!==A||0!=i&&n!=Ye){switch(R=-1,Je[D].Re){case 0:R=(e=>{let n,r=65535;for(r>s-5&&(r=s-5);;){if(1>=A){if(ie(),0===A&&0==e)return 0;if(0===A)break}if(C+=A,A=0,n=k+r,(0===C||C>=n)&&(A=C-n,C=n,se(!1),0===t.tt))return 0;if(C-k>=f-Ze&&(se(!1),0===t.tt))return 0}return se(4==e),0===t.tt?4==e?2:0:4==e?3:1})(i);break;case 1:R=(e=>{let n,r=0;for(;;){if(Ze>A){if(ie(),Ze>A&&0==e)return 0;if(0===A)break}if(3>A||(p=(p<<g^255&u[C+2])&b,r=65535&d[p],h[C&l]=d[p],d[p]=C),0===r||(C-r&65535)>f-Ze||2!=V&&(v=oe(r)),3>v)n=ee(0,255&u[C]),A--,C++;else if(n=ee(C-x,v-3),A-=v,v>P||3>A)C+=v,v=0,p=255&u[C],p=(p<<g^255&u[C+1])&b;else{v--;do{C++,p=(p<<g^255&u[C+2])&b,r=65535&d[p],h[C&l]=d[p],d[p]=C}while(0!=--v);C++}if(n&&(se(!1),0===t.tt))return 0}return se(4==e),0===t.tt?4==e?2:0:4==e?3:1})(i);break;case 2:R=(e=>{let n,r,s=0;for(;;){if(Ze>A){if(ie(),Ze>A&&0==e)return 0;if(0===A)break}if(3>A||(p=(p<<g^255&u[C+2])&b,s=65535&d[p],h[C&l]=d[p],d[p]=C),_=v,S=x,v=2,0!==s&&P>_&&f-Ze>=(C-s&65535)&&(2!=V&&(v=oe(s)),5>=v&&(1==V||3==v&&C-x>4096)&&(v=2)),3>_||v>_)if(0!==z){if(n=ee(0,255&u[C-1]),n&&se(!1),C++,A--,0===t.tt)return 0}else z=1,C++,A--;else{r=C+A-3,n=ee(C-1-S,_-3),A-=_-1,_-=2;do{++C>r||(p=(p<<g^255&u[C+2])&b,s=65535&d[p],h[C&l]=d[p],d[p]=C)}while(0!=--_);if(z=0,v=2,C++,n&&(se(!1),0===t.tt))return 0}}return 0!==z&&(n=ee(0,255&u[C-1]),z=0),se(4==e),0===t.tt?4==e?2:0:4==e?3:1})(i)}if(2!=R&&3!=R||(n=Ye),0==R||2==R)return 0===t.tt&&(c=-1),0;if(1==R){if(1==i)X(2,3),Y(256,Le._e),$(),9>1+H+10-F&&(X(2,3),Y(256,Le._e),$()),H=7;else if(re(0,0,!1),3==i)for(o=0;y>o;o++)d[o]=0;if(t.Te(),0===t.tt)return c=-1,0}}return 4!=i?0:1}}function tt(){const e=this;e.nt=0,e.rt=0,e.We=0,e.qe=0,e.tt=0,e.Ge=0}function nt(e){const t=new tt,n=(o=e&&e.chunkSize?e.chunkSize:65536)+5*(r.floor(o/16383)+1);var o;const c=new i(n);let f=e?e.level:-1;void 0===f&&(f=-1),t.He(f),t.$e=c,this.append=(e,r)=>{let o,f,a=0,l=0,u=0;const w=[];if(e.length){t.nt=0,t.et=e,t.We=e.length;do{if(t.rt=0,t.tt=n,o=t.Ye(0),0!=o)throw new s("deflating: "+t.Le);t.rt&&(t.rt==n?w.push(new i(c)):w.push(c.subarray(0,t.rt))),u+=t.rt,r&&t.nt>0&&t.nt!=a&&(r(t.nt),a=t.nt)}while(t.We>0||0===t.tt);return w.length>1?(f=new i(u),w.forEach((e=>{f.set(e,l),l+=e.length}))):f=w[0]?new i(w[0]):new i,f}},this.flush=()=>{let e,r,o=0,f=0;const a=[];do{if(t.rt=0,t.tt=n,e=t.Ye(4),1!=e&&0!=e)throw new s("deflating: "+t.Le);n-t.tt>0&&a.push(c.slice(0,t.rt)),f+=t.rt}while(t.We>0||0===t.tt);return t.Qe(),r=new i(f),a.forEach((e=>{r.set(e,o),o+=e.length})),r}}tt.prototype={He(e,t){const n=this;return n.Fe=new et,t||(t=15),n.Fe.He(n,e,t)},Ye(e){const t=this;return t.Fe?t.Fe.Ye(t,e):Oe},Qe(){const e=this;if(!e.Fe)return Oe;const t=e.Fe.Qe();return e.Fe=null,t},Xe(e,t){const n=this;return n.Fe?n.Fe.Xe(n,e,t):Oe},Ze(e,t){const n=this;return n.Fe?n.Fe.Ze(n,e,t):Oe},je(e,t,n){const r=this;let s=r.We;return s>n&&(s=n),0===s?0:(r.We-=s,e.set(r.et.subarray(r.nt,r.nt+s),t),r.nt+=s,r.qe+=s,s)},Te(){const e=this;let t=e.Fe.pending;t>e.tt&&(t=e.tt),0!==t&&(e.$e.set(e.Fe.Ke.subarray(e.Fe.Je,e.Fe.Je+t),e.rt),e.rt+=t,e.Fe.Je+=t,e.Ge+=t,e.tt-=t,e.Fe.pending-=t,0===e.Fe.pending&&(e.Fe.Je=0))}};const rt=-2,st=-3,it=-5,ot=[0,1,3,7,15,31,63,127,255,511,1023,2047,4095,8191,16383,32767,65535],ct=[96,7,256,0,8,80,0,8,16,84,8,115,82,7,31,0,8,112,0,8,48,0,9,192,80,7,10,0,8,96,0,8,32,0,9,160,0,8,0,0,8,128,0,8,64,0,9,224,80,7,6,0,8,88,0,8,24,0,9,144,83,7,59,0,8,120,0,8,56,0,9,208,81,7,17,0,8,104,0,8,40,0,9,176,0,8,8,0,8,136,0,8,72,0,9,240,80,7,4,0,8,84,0,8,20,85,8,227,83,7,43,0,8,116,0,8,52,0,9,200,81,7,13,0,8,100,0,8,36,0,9,168,0,8,4,0,8,132,0,8,68,0,9,232,80,7,8,0,8,92,0,8,28,0,9,152,84,7,83,0,8,124,0,8,60,0,9,216,82,7,23,0,8,108,0,8,44,0,9,184,0,8,12,0,8,140,0,8,76,0,9,248,80,7,3,0,8,82,0,8,18,85,8,163,83,7,35,0,8,114,0,8,50,0,9,196,81,7,11,0,8,98,0,8,34,0,9,164,0,8,2,0,8,130,0,8,66,0,9,228,80,7,7,0,8,90,0,8,26,0,9,148,84,7,67,0,8,122,0,8,58,0,9,212,82,7,19,0,8,106,0,8,42,0,9,180,0,8,10,0,8,138,0,8,74,0,9,244,80,7,5,0,8,86,0,8,22,192,8,0,83,7,51,0,8,118,0,8,54,0,9,204,81,7,15,0,8,102,0,8,38,0,9,172,0,8,6,0,8,134,0,8,70,0,9,236,80,7,9,0,8,94,0,8,30,0,9,156,84,7,99,0,8,126,0,8,62,0,9,220,82,7,27,0,8,110,0,8,46,0,9,188,0,8,14,0,8,142,0,8,78,0,9,252,96,7,256,0,8,81,0,8,17,85,8,131,82,7,31,0,8,113,0,8,49,0,9,194,80,7,10,0,8,97,0,8,33,0,9,162,0,8,1,0,8,129,0,8,65,0,9,226,80,7,6,0,8,89,0,8,25,0,9,146,83,7,59,0,8,121,0,8,57,0,9,210,81,7,17,0,8,105,0,8,41,0,9,178,0,8,9,0,8,137,0,8,73,0,9,242,80,7,4,0,8,85,0,8,21,80,8,258,83,7,43,0,8,117,0,8,53,0,9,202,81,7,13,0,8,101,0,8,37,0,9,170,0,8,5,0,8,133,0,8,69,0,9,234,80,7,8,0,8,93,0,8,29,0,9,154,84,7,83,0,8,125,0,8,61,0,9,218,82,7,23,0,8,109,0,8,45,0,9,186,0,8,13,0,8,141,0,8,77,0,9,250,80,7,3,0,8,83,0,8,19,85,8,195,83,7,35,0,8,115,0,8,51,0,9,198,81,7,11,0,8,99,0,8,35,0,9,166,0,8,3,0,8,131,0,8,67,0,9,230,80,7,7,0,8,91,0,8,27,0,9,150,84,7,67,0,8,123,0,8,59,0,9,214,82,7,19,0,8,107,0,8,43,0,9,182,0,8,11,0,8,139,0,8,75,0,9,246,80,7,5,0,8,87,0,8,23,192,8,0,83,7,51,0,8,119,0,8,55,0,9,206,81,7,15,0,8,103,0,8,39,0,9,174,0,8,7,0,8,135,0,8,71,0,9,238,80,7,9,0,8,95,0,8,31,0,9,158,84,7,99,0,8,127,0,8,63,0,9,222,82,7,27,0,8,111,0,8,47,0,9,190,0,8,15,0,8,143,0,8,79,0,9,254,96,7,256,0,8,80,0,8,16,84,8,115,82,7,31,0,8,112,0,8,48,0,9,193,80,7,10,0,8,96,0,8,32,0,9,161,0,8,0,0,8,128,0,8,64,0,9,225,80,7,6,0,8,88,0,8,24,0,9,145,83,7,59,0,8,120,0,8,56,0,9,209,81,7,17,0,8,104,0,8,40,0,9,177,0,8,8,0,8,136,0,8,72,0,9,241,80,7,4,0,8,84,0,8,20,85,8,227,83,7,43,0,8,116,0,8,52,0,9,201,81,7,13,0,8,100,0,8,36,0,9,169,0,8,4,0,8,132,0,8,68,0,9,233,80,7,8,0,8,92,0,8,28,0,9,153,84,7,83,0,8,124,0,8,60,0,9,217,82,7,23,0,8,108,0,8,44,0,9,185,0,8,12,0,8,140,0,8,76,0,9,249,80,7,3,0,8,82,0,8,18,85,8,163,83,7,35,0,8,114,0,8,50,0,9,197,81,7,11,0,8,98,0,8,34,0,9,165,0,8,2,0,8,130,0,8,66,0,9,229,80,7,7,0,8,90,0,8,26,0,9,149,84,7,67,0,8,122,0,8,58,0,9,213,82,7,19,0,8,106,0,8,42,0,9,181,0,8,10,0,8,138,0,8,74,0,9,245,80,7,5,0,8,86,0,8,22,192,8,0,83,7,51,0,8,118,0,8,54,0,9,205,81,7,15,0,8,102,0,8,38,0,9,173,0,8,6,0,8,134,0,8,70,0,9,237,80,7,9,0,8,94,0,8,30,0,9,157,84,7,99,0,8,126,0,8,62,0,9,221,82,7,27,0,8,110,0,8,46,0,9,189,0,8,14,0,8,142,0,8,78,0,9,253,96,7,256,0,8,81,0,8,17,85,8,131,82,7,31,0,8,113,0,8,49,0,9,195,80,7,10,0,8,97,0,8,33,0,9,163,0,8,1,0,8,129,0,8,65,0,9,227,80,7,6,0,8,89,0,8,25,0,9,147,83,7,59,0,8,121,0,8,57,0,9,211,81,7,17,0,8,105,0,8,41,0,9,179,0,8,9,0,8,137,0,8,73,0,9,243,80,7,4,0,8,85,0,8,21,80,8,258,83,7,43,0,8,117,0,8,53,0,9,203,81,7,13,0,8,101,0,8,37,0,9,171,0,8,5,0,8,133,0,8,69,0,9,235,80,7,8,0,8,93,0,8,29,0,9,155,84,7,83,0,8,125,0,8,61,0,9,219,82,7,23,0,8,109,0,8,45,0,9,187,0,8,13,0,8,141,0,8,77,0,9,251,80,7,3,0,8,83,0,8,19,85,8,195,83,7,35,0,8,115,0,8,51,0,9,199,81,7,11,0,8,99,0,8,35,0,9,167,0,8,3,0,8,131,0,8,67,0,9,231,80,7,7,0,8,91,0,8,27,0,9,151,84,7,67,0,8,123,0,8,59,0,9,215,82,7,19,0,8,107,0,8,43,0,9,183,0,8,11,0,8,139,0,8,75,0,9,247,80,7,5,0,8,87,0,8,23,192,8,0,83,7,51,0,8,119,0,8,55,0,9,207,81,7,15,0,8,103,0,8,39,0,9,175,0,8,7,0,8,135,0,8,71,0,9,239,80,7,9,0,8,95,0,8,31,0,9,159,84,7,99,0,8,127,0,8,63,0,9,223,82,7,27,0,8,111,0,8,47,0,9,191,0,8,15,0,8,143,0,8,79,0,9,255],ft=[80,5,1,87,5,257,83,5,17,91,5,4097,81,5,5,89,5,1025,85,5,65,93,5,16385,80,5,3,88,5,513,84,5,33,92,5,8193,82,5,9,90,5,2049,86,5,129,192,5,24577,80,5,2,87,5,385,83,5,25,91,5,6145,81,5,7,89,5,1537,85,5,97,93,5,24577,80,5,4,88,5,769,84,5,49,92,5,12289,82,5,13,90,5,3073,86,5,193,192,5,24577],at=[3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258,0,0],lt=[0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0,112,112],ut=[1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577],wt=[0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13];function ht(){let e,t,n,r,s,i;function o(e,t,o,c,f,a,l,u,w,h,d){let p,y,m,b,g,k,v,S,z,C,x,A,_,I,P;C=0,g=o;do{n[e[t+C]]++,C++,g--}while(0!==g);if(n[0]==o)return l[0]=-1,u[0]=0,0;for(S=u[0],k=1;15>=k&&0===n[k];k++);for(v=k,k>S&&(S=k),g=15;0!==g&&0===n[g];g--);for(m=g,S>g&&(S=g),u[0]=S,I=1<<k;g>k;k++,I<<=1)if(0>(I-=n[k]))return st;if(0>(I-=n[g]))return st;for(n[g]+=I,i[1]=k=0,C=1,_=2;0!=--g;)i[_]=k+=n[C],_++,C++;g=0,C=0;do{0!==(k=e[t+C])&&(d[i[k]++]=g),C++}while(++g<o);for(o=i[m],i[0]=g=0,C=0,b=-1,A=-S,s[0]=0,x=0,P=0;m>=v;v++)for(p=n[v];0!=p--;){for(;v>A+S;){if(b++,A+=S,P=m-A,P=P>S?S:P,(y=1<<(k=v-A))>p+1&&(y-=p+1,_=v,P>k))for(;++k<P&&(y<<=1)>n[++_];)y-=n[_];if(P=1<<k,h[0]+P>1440)return st;s[b]=x=h[0],h[0]+=P,0!==b?(i[b]=g,r[0]=k,r[1]=S,k=g>>>A-S,r[2]=x-s[b-1]-k,w.set(r,3*(s[b-1]+k))):l[0]=x}for(r[1]=v-A,o>C?d[C]<c?(r[0]=256>d[C]?0:96,r[2]=d[C++]):(r[0]=a[d[C]-c]+16+64,r[2]=f[d[C++]-c]):r[0]=192,y=1<<v-A,k=g>>>A;P>k;k+=y)w.set(r,3*(x+k));for(k=1<<v-1;g&k;k>>>=1)g^=k;for(g^=k,z=(1<<A)-1;(g&z)!=i[b];)b--,A-=S,z=(1<<A)-1}return 0!==I&&1!=m?it:0}function c(o){let c;for(e||(e=[],t=[],n=new f(16),r=[],s=new f(15),i=new f(16)),t.length<o&&(t=[]),c=0;o>c;c++)t[c]=0;for(c=0;16>c;c++)n[c]=0;for(c=0;3>c;c++)r[c]=0;s.set(n.subarray(0,15),0),i.set(n.subarray(0,16),0)}this.st=(n,r,s,i,f)=>{let a;return c(19),e[0]=0,a=o(n,0,19,19,null,null,s,r,i,e,t),a==st?f.Le="oversubscribed dynamic bit lengths tree":a!=it&&0!==r[0]||(f.Le="incomplete dynamic bit lengths tree",a=st),a},this.it=(n,r,s,i,f,a,l,u,w)=>{let h;return c(288),e[0]=0,h=o(s,0,n,257,at,lt,a,i,u,e,t),0!=h||0===i[0]?(h==st?w.Le="oversubscribed literal/length tree":-4!=h&&(w.Le="incomplete literal/length tree",h=st),h):(c(288),h=o(s,n,r,0,ut,wt,l,f,u,e,t),0!=h||0===f[0]&&n>257?(h==st?w.Le="oversubscribed distance tree":h==it?(w.Le="incomplete distance tree",h=st):-4!=h&&(w.Le="empty distance tree with lengths",h=st),h):0)}}function dt(){const e=this;let t,n,r,s,i=0,o=0,c=0,f=0,a=0,l=0,u=0,w=0,h=0,d=0;function p(e,t,n,r,s,i,o,c){let f,a,l,u,w,h,d,p,y,m,b,g,k,v,S,z;d=c.nt,p=c.We,w=o.ot,h=o.ct,y=o.write,m=y<o.read?o.read-y-1:o.end-y,b=ot[e],g=ot[t];do{for(;20>h;)p--,w|=(255&c.ft(d++))<<h,h+=8;if(f=w&b,a=n,l=r,z=3*(l+f),0!==(u=a[z]))for(;;){if(w>>=a[z+1],h-=a[z+1],16&u){for(u&=15,k=a[z+2]+(w&ot[u]),w>>=u,h-=u;15>h;)p--,w|=(255&c.ft(d++))<<h,h+=8;for(f=w&g,a=s,l=i,z=3*(l+f),u=a[z];;){if(w>>=a[z+1],h-=a[z+1],16&u){for(u&=15;u>h;)p--,w|=(255&c.ft(d++))<<h,h+=8;if(v=a[z+2]+(w&ot[u]),w>>=u,h-=u,m-=k,v>y){S=y-v;do{S+=o.end}while(0>S);if(u=o.end-S,k>u){if(k-=u,y-S>0&&u>y-S)do{o.lt[y++]=o.lt[S++]}while(0!=--u);else o.lt.set(o.lt.subarray(S,S+u),y),y+=u,S+=u,u=0;S=0}}else S=y-v,y-S>0&&2>y-S?(o.lt[y++]=o.lt[S++],o.lt[y++]=o.lt[S++],k-=2):(o.lt.set(o.lt.subarray(S,S+2),y),y+=2,S+=2,k-=2);if(y-S>0&&k>y-S)do{o.lt[y++]=o.lt[S++]}while(0!=--k);else o.lt.set(o.lt.subarray(S,S+k),y),y+=k,S+=k,k=0;break}if(64&u)return c.Le="invalid distance code",k=c.We-p,k=k>h>>3?h>>3:k,p+=k,d-=k,h-=k<<3,o.ot=w,o.ct=h,c.We=p,c.qe+=d-c.nt,c.nt=d,o.write=y,st;f+=a[z+2],f+=w&ot[u],z=3*(l+f),u=a[z]}break}if(64&u)return 32&u?(k=c.We-p,k=k>h>>3?h>>3:k,p+=k,d-=k,h-=k<<3,o.ot=w,o.ct=h,c.We=p,c.qe+=d-c.nt,c.nt=d,o.write=y,1):(c.Le="invalid literal/length code",k=c.We-p,k=k>h>>3?h>>3:k,p+=k,d-=k,h-=k<<3,o.ot=w,o.ct=h,c.We=p,c.qe+=d-c.nt,c.nt=d,o.write=y,st);if(f+=a[z+2],f+=w&ot[u],z=3*(l+f),0===(u=a[z])){w>>=a[z+1],h-=a[z+1],o.lt[y++]=a[z+2],m--;break}}else w>>=a[z+1],h-=a[z+1],o.lt[y++]=a[z+2],m--}while(m>=258&&p>=10);return k=c.We-p,k=k>h>>3?h>>3:k,p+=k,d-=k,h-=k<<3,o.ot=w,o.ct=h,c.We=p,c.qe+=d-c.nt,c.nt=d,o.write=y,0}e.init=(e,i,o,c,f,a)=>{t=0,u=e,w=i,r=o,h=c,s=f,d=a,n=null},e.ut=(e,y,m)=>{let b,g,k,v,S,z,C,x=0,A=0,_=0;for(_=y.nt,v=y.We,x=e.ot,A=e.ct,S=e.write,z=S<e.read?e.read-S-1:e.end-S;;)switch(t){case 0:if(z>=258&&v>=10&&(e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,m=p(u,w,r,h,s,d,e,y),_=y.nt,v=y.We,x=e.ot,A=e.ct,S=e.write,z=S<e.read?e.read-S-1:e.end-S,0!=m)){t=1==m?7:9;break}c=u,n=r,o=h,t=1;case 1:for(b=c;b>A;){if(0===v)return e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);m=0,v--,x|=(255&y.ft(_++))<<A,A+=8}if(g=3*(o+(x&ot[b])),x>>>=n[g+1],A-=n[g+1],k=n[g],0===k){f=n[g+2],t=6;break}if(16&k){a=15&k,i=n[g+2],t=2;break}if(!(64&k)){c=k,o=g/3+n[g+2];break}if(32&k){t=7;break}return t=9,y.Le="invalid literal/length code",m=st,e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);case 2:for(b=a;b>A;){if(0===v)return e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);m=0,v--,x|=(255&y.ft(_++))<<A,A+=8}i+=x&ot[b],x>>=b,A-=b,c=w,n=s,o=d,t=3;case 3:for(b=c;b>A;){if(0===v)return e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);m=0,v--,x|=(255&y.ft(_++))<<A,A+=8}if(g=3*(o+(x&ot[b])),x>>=n[g+1],A-=n[g+1],k=n[g],16&k){a=15&k,l=n[g+2],t=4;break}if(!(64&k)){c=k,o=g/3+n[g+2];break}return t=9,y.Le="invalid distance code",m=st,e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);case 4:for(b=a;b>A;){if(0===v)return e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);m=0,v--,x|=(255&y.ft(_++))<<A,A+=8}l+=x&ot[b],x>>=b,A-=b,t=5;case 5:for(C=S-l;0>C;)C+=e.end;for(;0!==i;){if(0===z&&(S==e.end&&0!==e.read&&(S=0,z=S<e.read?e.read-S-1:e.end-S),0===z&&(e.write=S,m=e.wt(y,m),S=e.write,z=S<e.read?e.read-S-1:e.end-S,S==e.end&&0!==e.read&&(S=0,z=S<e.read?e.read-S-1:e.end-S),0===z)))return e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);e.lt[S++]=e.lt[C++],z--,C==e.end&&(C=0),i--}t=0;break;case 6:if(0===z&&(S==e.end&&0!==e.read&&(S=0,z=S<e.read?e.read-S-1:e.end-S),0===z&&(e.write=S,m=e.wt(y,m),S=e.write,z=S<e.read?e.read-S-1:e.end-S,S==e.end&&0!==e.read&&(S=0,z=S<e.read?e.read-S-1:e.end-S),0===z)))return e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);m=0,e.lt[S++]=f,z--,t=0;break;case 7:if(A>7&&(A-=8,v++,_--),e.write=S,m=e.wt(y,m),S=e.write,z=S<e.read?e.read-S-1:e.end-S,e.read!=e.write)return e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);t=8;case 8:return m=1,e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);case 9:return m=st,e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m);default:return m=rt,e.ot=x,e.ct=A,y.We=v,y.qe+=_-y.nt,y.nt=_,e.write=S,e.wt(y,m)}},e.ht=()=>{}}ht.dt=(e,t,n,r)=>(e[0]=9,t[0]=5,n[0]=ct,r[0]=ft,0);const pt=[16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15];function yt(e,t){const n=this;let r,s=0,o=0,c=0,a=0;const l=[0],u=[0],w=new dt;let h=0,d=new f(4320);const p=new ht;n.ct=0,n.ot=0,n.lt=new i(t),n.end=t,n.read=0,n.write=0,n.reset=(e,t)=>{t&&(t[0]=0),6==s&&w.ht(e),s=0,n.ct=0,n.ot=0,n.read=n.write=0},n.reset(e,null),n.wt=(e,t)=>{let r,s,i;return s=e.rt,i=n.read,r=(i>n.write?n.end:n.write)-i,r>e.tt&&(r=e.tt),0!==r&&t==it&&(t=0),e.tt-=r,e.Ge+=r,e.$e.set(n.lt.subarray(i,i+r),s),s+=r,i+=r,i==n.end&&(i=0,n.write==n.end&&(n.write=0),r=n.write-i,r>e.tt&&(r=e.tt),0!==r&&t==it&&(t=0),e.tt-=r,e.Ge+=r,e.$e.set(n.lt.subarray(i,i+r),s),s+=r,i+=r),e.rt=s,n.read=i,t},n.ut=(e,t)=>{let i,f,y,m,b,g,k,v;for(m=e.nt,b=e.We,f=n.ot,y=n.ct,g=n.write,k=g<n.read?n.read-g-1:n.end-g;;){let S,z,C,x,A,_,I,P;switch(s){case 0:for(;3>y;){if(0===b)return n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);t=0,b--,f|=(255&e.ft(m++))<<y,y+=8}switch(i=7&f,h=1&i,i>>>1){case 0:f>>>=3,y-=3,i=7&y,f>>>=i,y-=i,s=1;break;case 1:S=[],z=[],C=[[]],x=[[]],ht.dt(S,z,C,x),w.init(S[0],z[0],C[0],0,x[0],0),f>>>=3,y-=3,s=6;break;case 2:f>>>=3,y-=3,s=3;break;case 3:return f>>>=3,y-=3,s=9,e.Le="invalid block type",t=st,n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t)}break;case 1:for(;32>y;){if(0===b)return n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);t=0,b--,f|=(255&e.ft(m++))<<y,y+=8}if((~f>>>16&65535)!=(65535&f))return s=9,e.Le="invalid stored block lengths",t=st,n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);o=65535&f,f=y=0,s=0!==o?2:0!==h?7:0;break;case 2:if(0===b)return n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);if(0===k&&(g==n.end&&0!==n.read&&(g=0,k=g<n.read?n.read-g-1:n.end-g),0===k&&(n.write=g,t=n.wt(e,t),g=n.write,k=g<n.read?n.read-g-1:n.end-g,g==n.end&&0!==n.read&&(g=0,k=g<n.read?n.read-g-1:n.end-g),0===k)))return n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);if(t=0,i=o,i>b&&(i=b),i>k&&(i=k),n.lt.set(e.je(m,i),g),m+=i,b-=i,g+=i,k-=i,0!=(o-=i))break;s=0!==h?7:0;break;case 3:for(;14>y;){if(0===b)return n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);t=0,b--,f|=(255&e.ft(m++))<<y,y+=8}if(c=i=16383&f,(31&i)>29||(i>>5&31)>29)return s=9,e.Le="too many length or distance symbols",t=st,n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);if(i=258+(31&i)+(i>>5&31),!r||r.length<i)r=[];else for(v=0;i>v;v++)r[v]=0;f>>>=14,y-=14,a=0,s=4;case 4:for(;4+(c>>>10)>a;){for(;3>y;){if(0===b)return n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);t=0,b--,f|=(255&e.ft(m++))<<y,y+=8}r[pt[a++]]=7&f,f>>>=3,y-=3}for(;19>a;)r[pt[a++]]=0;if(l[0]=7,i=p.st(r,l,u,d,e),0!=i)return(t=i)==st&&(r=null,s=9),n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);a=0,s=5;case 5:for(;i=c,258+(31&i)+(i>>5&31)>a;){let o,w;for(i=l[0];i>y;){if(0===b)return n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);t=0,b--,f|=(255&e.ft(m++))<<y,y+=8}if(i=d[3*(u[0]+(f&ot[i]))+1],w=d[3*(u[0]+(f&ot[i]))+2],16>w)f>>>=i,y-=i,r[a++]=w;else{for(v=18==w?7:w-14,o=18==w?11:3;i+v>y;){if(0===b)return n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);t=0,b--,f|=(255&e.ft(m++))<<y,y+=8}if(f>>>=i,y-=i,o+=f&ot[v],f>>>=v,y-=v,v=a,i=c,v+o>258+(31&i)+(i>>5&31)||16==w&&1>v)return r=null,s=9,e.Le="invalid bit length repeat",t=st,n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);w=16==w?r[v-1]:0;do{r[v++]=w}while(0!=--o);a=v}}if(u[0]=-1,A=[],_=[],I=[],P=[],A[0]=9,_[0]=6,i=c,i=p.it(257+(31&i),1+(i>>5&31),r,A,_,I,P,d,e),0!=i)return i==st&&(r=null,s=9),t=i,n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);w.init(A[0],_[0],d,I[0],d,P[0]),s=6;case 6:if(n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,1!=(t=w.ut(n,e,t)))return n.wt(e,t);if(t=0,w.ht(e),m=e.nt,b=e.We,f=n.ot,y=n.ct,g=n.write,k=g<n.read?n.read-g-1:n.end-g,0===h){s=0;break}s=7;case 7:if(n.write=g,t=n.wt(e,t),g=n.write,k=g<n.read?n.read-g-1:n.end-g,n.read!=n.write)return n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);s=8;case 8:return t=1,n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);case 9:return t=st,n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t);default:return t=rt,n.ot=f,n.ct=y,e.We=b,e.qe+=m-e.nt,e.nt=m,n.write=g,n.wt(e,t)}}},n.ht=e=>{n.reset(e,null),n.lt=null,d=null},n.yt=(e,t,r)=>{n.lt.set(e.subarray(t,t+r),0),n.read=n.write=r},n.bt=()=>1==s?1:0}const mt=13,bt=[0,0,255,255];function gt(){const e=this;function t(e){return e&&e.gt?(e.qe=e.Ge=0,e.Le=null,e.gt.mode=7,e.gt.kt.reset(e,null),0):rt}e.mode=0,e.method=0,e.vt=[0],e.St=0,e.marker=0,e.zt=0,e.Ct=t=>(e.kt&&e.kt.ht(t),e.kt=null,0),e.xt=(n,r)=>(n.Le=null,e.kt=null,8>r||r>15?(e.Ct(n),rt):(e.zt=r,n.gt.kt=new yt(n,1<<r),t(n),0)),e.At=(e,t)=>{let n,r;if(!e||!e.gt||!e.et)return rt;const s=e.gt;for(t=4==t?it:0,n=it;;)switch(s.mode){case 0:if(0===e.We)return n;if(n=t,e.We--,e.qe++,8!=(15&(s.method=e.ft(e.nt++)))){s.mode=mt,e.Le="unknown compression method",s.marker=5;break}if(8+(s.method>>4)>s.zt){s.mode=mt,e.Le="invalid win size",s.marker=5;break}s.mode=1;case 1:if(0===e.We)return n;if(n=t,e.We--,e.qe++,r=255&e.ft(e.nt++),((s.method<<8)+r)%31!=0){s.mode=mt,e.Le="incorrect header check",s.marker=5;break}if(!(32&r)){s.mode=7;break}s.mode=2;case 2:if(0===e.We)return n;n=t,e.We--,e.qe++,s.St=(255&e.ft(e.nt++))<<24&4278190080,s.mode=3;case 3:if(0===e.We)return n;n=t,e.We--,e.qe++,s.St+=(255&e.ft(e.nt++))<<16&16711680,s.mode=4;case 4:if(0===e.We)return n;n=t,e.We--,e.qe++,s.St+=(255&e.ft(e.nt++))<<8&65280,s.mode=5;case 5:return 0===e.We?n:(n=t,e.We--,e.qe++,s.St+=255&e.ft(e.nt++),s.mode=6,2);case 6:return s.mode=mt,e.Le="need dictionary",s.marker=0,rt;case 7:if(n=s.kt.ut(e,n),n==st){s.mode=mt,s.marker=0;break}if(0==n&&(n=t),1!=n)return n;n=t,s.kt.reset(e,s.vt),s.mode=12;case 12:return e.We=0,1;case mt:return st;default:return rt}},e._t=(e,t,n)=>{let r=0,s=n;if(!e||!e.gt||6!=e.gt.mode)return rt;const i=e.gt;return s<1<<i.zt||(s=(1<<i.zt)-1,r=n-s),i.kt.yt(t,r,s),i.mode=7,0},e.It=e=>{let n,r,s,i,o;if(!e||!e.gt)return rt;const c=e.gt;if(c.mode!=mt&&(c.mode=mt,c.marker=0),0===(n=e.We))return it;for(r=e.nt,s=c.marker;0!==n&&4>s;)e.ft(r)==bt[s]?s++:s=0!==e.ft(r)?0:4-s,r++,n--;return e.qe+=r-e.nt,e.nt=r,e.We=n,c.marker=s,4!=s?st:(i=e.qe,o=e.Ge,t(e),e.qe=i,e.Ge=o,c.mode=7,0)},e.Pt=e=>e&&e.gt&&e.gt.kt?e.gt.kt.bt():rt}function kt(){}function vt(e){const t=new kt,n=e&&e.chunkSize?r.floor(2*e.chunkSize):131072,o=new i(n);let c=!1;t.xt(),t.$e=o,this.append=(e,r)=>{const f=[];let a,l,u=0,w=0,h=0;if(0!==e.length){t.nt=0,t.et=e,t.We=e.length;do{if(t.rt=0,t.tt=n,0!==t.We||c||(t.nt=0,c=!0),a=t.At(0),c&&a===it){if(0!==t.We)throw new s("inflating: bad input")}else if(0!==a&&1!==a)throw new s("inflating: "+t.Le);if((c||1===a)&&t.We===e.length)throw new s("inflating: bad input");t.rt&&(t.rt===n?f.push(new i(o)):f.push(o.subarray(0,t.rt))),h+=t.rt,r&&t.nt>0&&t.nt!=u&&(r(t.nt),u=t.nt)}while(t.We>0||0===t.tt);return f.length>1?(l=new i(h),f.forEach((e=>{l.set(e,w),w+=e.length}))):l=f[0]?new i(f[0]):new i,l}},this.flush=()=>{t.Ct()}}kt.prototype={xt(e){const t=this;return t.gt=new gt,e||(e=15),t.gt.xt(t,e)},At(e){const t=this;return t.gt?t.gt.At(t,e):rt},Ct(){const e=this;if(!e.gt)return rt;const t=e.gt.Ct(e);return e.gt=null,t},It(){const e=this;return e.gt?e.gt.It(e):rt},_t(e,t){const n=this;return n.gt?n.gt._t(n,e,t):rt},ft(e){return this.et[e]},je(e,t){return this.et.subarray(e,e+t)}},self.initCodec=()=>{self.Deflate=nt,self.Inflate=vt};\n', r = () => t.useDataURI ? "data:text/javascript," + encodeURIComponent(n) : URL.createObjectURL(new Blob([n], { type: "text/javascript" }));
  e2({ workerScripts: { inflate: [r], deflate: [r] } });
}

// node_modules/@zip.js/zip.js/lib/core/io.js
var ERR_ITERATOR_COMPLETED_TOO_SOON = "Writer iterator completed too soon";
var HTTP_HEADER_CONTENT_TYPE = "Content-Type";
var DEFAULT_CHUNK_SIZE = 64 * 1024;
var PROPERTY_NAME_WRITABLE = "writable";
var Stream = class {
  constructor() {
    this.size = 0;
  }
  init() {
    this.initialized = true;
  }
};
var Reader = class extends Stream {
  get readable() {
    const reader = this;
    const { chunkSize = DEFAULT_CHUNK_SIZE } = reader;
    const readable = new ReadableStream({
      start() {
        this.chunkOffset = 0;
      },
      async pull(controller) {
        const { offset = 0, size, diskNumberStart } = readable;
        const { chunkOffset } = this;
        const dataSize = size === UNDEFINED_VALUE ? chunkSize : Math.min(chunkSize, size - chunkOffset);
        const data = await readUint8Array(reader, offset + chunkOffset, dataSize, diskNumberStart);
        controller.enqueue(data);
        if (chunkOffset + chunkSize > size || size === UNDEFINED_VALUE && !data.length && dataSize) {
          controller.close();
        } else {
          this.chunkOffset += chunkSize;
        }
      }
    });
    return readable;
  }
};
var BlobReader = class extends Reader {
  constructor(blob) {
    super();
    Object.assign(this, {
      blob,
      size: blob.size
    });
  }
  async readUint8Array(offset, length) {
    const reader = this;
    const offsetEnd = offset + length;
    const blob = offset || offsetEnd < reader.size ? reader.blob.slice(offset, offsetEnd) : reader.blob;
    let arrayBuffer = await blob.arrayBuffer();
    if (arrayBuffer.byteLength > length) {
      arrayBuffer = arrayBuffer.slice(offset, offsetEnd);
    }
    return new Uint8Array(arrayBuffer);
  }
};
var BlobWriter = class extends Stream {
  constructor(contentType) {
    super();
    const writer = this;
    const transformStream = new TransformStream();
    const headers = [];
    if (contentType) {
      headers.push([HTTP_HEADER_CONTENT_TYPE, contentType]);
    }
    Object.defineProperty(writer, PROPERTY_NAME_WRITABLE, {
      get() {
        return transformStream.writable;
      }
    });
    writer.blob = new Response(transformStream.readable, { headers }).blob();
  }
  getData() {
    return this.blob;
  }
};
var TextWriter = class extends BlobWriter {
  constructor(encoding) {
    super(encoding);
    Object.assign(this, {
      encoding,
      utf8: !encoding || encoding.toLowerCase() == "utf-8"
    });
  }
  async getData() {
    const {
      encoding,
      utf8
    } = this;
    const blob = await super.getData();
    if (blob.text && utf8) {
      return blob.text();
    } else {
      const reader = new FileReader();
      return new Promise((resolve, reject) => {
        Object.assign(reader, {
          onload: ({ target }) => resolve(target.result),
          onerror: () => reject(reader.error)
        });
        reader.readAsText(blob, encoding);
      });
    }
  }
};
var SplitDataReader = class extends Reader {
  constructor(readers) {
    super();
    this.readers = readers;
  }
  async init() {
    const reader = this;
    const { readers } = reader;
    reader.lastDiskNumber = 0;
    reader.lastDiskOffset = 0;
    await Promise.all(readers.map(async (diskReader, indexDiskReader) => {
      await diskReader.init();
      if (indexDiskReader != readers.length - 1) {
        reader.lastDiskOffset += diskReader.size;
      }
      reader.size += diskReader.size;
    }));
    super.init();
  }
  async readUint8Array(offset, length, diskNumber = 0) {
    const reader = this;
    const { readers } = this;
    let result;
    let currentDiskNumber = diskNumber;
    if (currentDiskNumber == -1) {
      currentDiskNumber = readers.length - 1;
    }
    let currentReaderOffset = offset;
    while (currentReaderOffset >= readers[currentDiskNumber].size) {
      currentReaderOffset -= readers[currentDiskNumber].size;
      currentDiskNumber++;
    }
    const currentReader = readers[currentDiskNumber];
    const currentReaderSize = currentReader.size;
    if (currentReaderOffset + length <= currentReaderSize) {
      result = await readUint8Array(currentReader, currentReaderOffset, length);
    } else {
      const chunkLength = currentReaderSize - currentReaderOffset;
      result = new Uint8Array(length);
      result.set(await readUint8Array(currentReader, currentReaderOffset, chunkLength));
      result.set(await reader.readUint8Array(offset + chunkLength, length - chunkLength, diskNumber), chunkLength);
    }
    reader.lastDiskNumber = Math.max(currentDiskNumber, reader.lastDiskNumber);
    return result;
  }
};
var SplitDataWriter = class extends Stream {
  constructor(writerGenerator, maxSize = 4294967295) {
    super();
    const writer = this;
    Object.assign(writer, {
      diskNumber: 0,
      diskOffset: 0,
      size: 0,
      maxSize,
      availableSize: maxSize
    });
    let diskSourceWriter, diskWritable, diskWriter;
    const writable = new WritableStream({
      async write(chunk) {
        const { availableSize } = writer;
        if (!diskWriter) {
          const { value, done } = await writerGenerator.next();
          if (done && !value) {
            throw new Error(ERR_ITERATOR_COMPLETED_TOO_SOON);
          } else {
            diskSourceWriter = value;
            diskSourceWriter.size = 0;
            if (diskSourceWriter.maxSize) {
              writer.maxSize = diskSourceWriter.maxSize;
            }
            writer.availableSize = writer.maxSize;
            await initStream(diskSourceWriter);
            diskWritable = value.writable;
            diskWriter = diskWritable.getWriter();
          }
          await this.write(chunk);
        } else if (chunk.length >= availableSize) {
          await writeChunk(chunk.slice(0, availableSize));
          await closeDisk();
          writer.diskOffset += diskSourceWriter.size;
          writer.diskNumber++;
          diskWriter = null;
          await this.write(chunk.slice(availableSize));
        } else {
          await writeChunk(chunk);
        }
      },
      async close() {
        await diskWriter.ready;
        await closeDisk();
      }
    });
    Object.defineProperty(writer, PROPERTY_NAME_WRITABLE, {
      get() {
        return writable;
      }
    });
    async function writeChunk(chunk) {
      const chunkLength = chunk.length;
      if (chunkLength) {
        await diskWriter.ready;
        await diskWriter.write(chunk);
        diskSourceWriter.size += chunkLength;
        writer.size += chunkLength;
        writer.availableSize -= chunkLength;
      }
    }
    async function closeDisk() {
      diskWritable.size = diskSourceWriter.size;
      await diskWriter.close();
    }
  }
};
async function initStream(stream, initSize) {
  if (stream.init && !stream.initialized) {
    await stream.init(initSize);
  } else {
    return Promise.resolve();
  }
}
function initReader(reader) {
  if (Array.isArray(reader)) {
    reader = new SplitDataReader(reader);
  }
  if (reader instanceof ReadableStream) {
    reader = {
      readable: reader
    };
  }
  return reader;
}
function initWriter(writer) {
  if (writer.writable === UNDEFINED_VALUE && typeof writer.next == FUNCTION_TYPE) {
    writer = new SplitDataWriter(writer);
  }
  if (writer instanceof WritableStream) {
    writer = {
      writable: writer
    };
  }
  const { writable } = writer;
  if (writable.size === UNDEFINED_VALUE) {
    writable.size = 0;
  }
  if (!(writer instanceof SplitDataWriter)) {
    Object.assign(writer, {
      diskNumber: 0,
      diskOffset: 0,
      availableSize: Infinity,
      maxSize: Infinity
    });
  }
  return writer;
}
function readUint8Array(reader, offset, size, diskNumber) {
  return reader.readUint8Array(offset, size, diskNumber);
}

// node_modules/@zip.js/zip.js/lib/core/util/cp437-decode.js
var CP437 = "\0\u263A\u263B\u2665\u2666\u2663\u2660\u2022\u25D8\u25CB\u25D9\u2642\u2640\u266A\u266B\u263C\u25BA\u25C4\u2195\u203C\xB6\xA7\u25AC\u21A8\u2191\u2193\u2192\u2190\u221F\u2194\u25B2\u25BC !\"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~\u2302\xC7\xFC\xE9\xE2\xE4\xE0\xE5\xE7\xEA\xEB\xE8\xEF\xEE\xEC\xC4\xC5\xC9\xE6\xC6\xF4\xF6\xF2\xFB\xF9\xFF\xD6\xDC\xA2\xA3\xA5\u20A7\u0192\xE1\xED\xF3\xFA\xF1\xD1\xAA\xBA\xBF\u2310\xAC\xBD\xBC\xA1\xAB\xBB\u2591\u2592\u2593\u2502\u2524\u2561\u2562\u2556\u2555\u2563\u2551\u2557\u255D\u255C\u255B\u2510\u2514\u2534\u252C\u251C\u2500\u253C\u255E\u255F\u255A\u2554\u2569\u2566\u2560\u2550\u256C\u2567\u2568\u2564\u2565\u2559\u2558\u2552\u2553\u256B\u256A\u2518\u250C\u2588\u2584\u258C\u2590\u2580\u03B1\xDF\u0393\u03C0\u03A3\u03C3\xB5\u03C4\u03A6\u0398\u03A9\u03B4\u221E\u03C6\u03B5\u2229\u2261\xB1\u2265\u2264\u2320\u2321\xF7\u2248\xB0\u2219\xB7\u221A\u207F\xB2\u25A0 ".split("");
var VALID_CP437 = CP437.length == 256;
function decodeCP437(stringValue) {
  if (VALID_CP437) {
    let result = "";
    for (let indexCharacter = 0; indexCharacter < stringValue.length; indexCharacter++) {
      result += CP437[stringValue[indexCharacter]];
    }
    return result;
  } else {
    return new TextDecoder().decode(stringValue);
  }
}

// node_modules/@zip.js/zip.js/lib/core/util/decode-text.js
function decodeText(value, encoding) {
  if (encoding && encoding.trim().toLowerCase() == "cp437") {
    return decodeCP437(value);
  } else {
    return new TextDecoder(encoding).decode(value);
  }
}

// node_modules/@zip.js/zip.js/lib/core/zip-entry.js
var PROPERTY_NAME_FILENAME = "filename";
var PROPERTY_NAME_RAW_FILENAME = "rawFilename";
var PROPERTY_NAME_COMMENT = "comment";
var PROPERTY_NAME_RAW_COMMENT = "rawComment";
var PROPERTY_NAME_UNCOMPPRESSED_SIZE = "uncompressedSize";
var PROPERTY_NAME_COMPPRESSED_SIZE = "compressedSize";
var PROPERTY_NAME_OFFSET = "offset";
var PROPERTY_NAME_DISK_NUMBER_START = "diskNumberStart";
var PROPERTY_NAME_LAST_MODIFICATION_DATE = "lastModDate";
var PROPERTY_NAME_RAW_LAST_MODIFICATION_DATE = "rawLastModDate";
var PROPERTY_NAME_LAST_ACCESS_DATE = "lastAccessDate";
var PROPERTY_NAME_RAW_LAST_ACCESS_DATE = "rawLastAccessDate";
var PROPERTY_NAME_CREATION_DATE = "creationDate";
var PROPERTY_NAME_RAW_CREATION_DATE = "rawCreationDate";
var PROPERTY_NAME_INTERNAL_FILE_ATTRIBUTE = "internalFileAttribute";
var PROPERTY_NAME_INTERNAL_FILE_ATTRIBUTES = "internalFileAttributes";
var PROPERTY_NAME_EXTERNAL_FILE_ATTRIBUTE = "externalFileAttribute";
var PROPERTY_NAME_EXTERNAL_FILE_ATTRIBUTES = "externalFileAttributes";
var PROPERTY_NAME_MS_DOS_COMPATIBLE = "msDosCompatible";
var PROPERTY_NAME_ZIP64 = "zip64";
var PROPERTY_NAME_ENCRYPTED = "encrypted";
var PROPERTY_NAME_VERSION = "version";
var PROPERTY_NAME_VERSION_MADE_BY = "versionMadeBy";
var PROPERTY_NAME_ZIPCRYPTO = "zipCrypto";
var PROPERTY_NAME_DIRECTORY = "directory";
var PROPERTY_NAME_EXECUTABLE = "executable";
var PROPERTY_NAMES = [
  PROPERTY_NAME_FILENAME,
  PROPERTY_NAME_RAW_FILENAME,
  PROPERTY_NAME_COMPPRESSED_SIZE,
  PROPERTY_NAME_UNCOMPPRESSED_SIZE,
  PROPERTY_NAME_LAST_MODIFICATION_DATE,
  PROPERTY_NAME_RAW_LAST_MODIFICATION_DATE,
  PROPERTY_NAME_COMMENT,
  PROPERTY_NAME_RAW_COMMENT,
  PROPERTY_NAME_LAST_ACCESS_DATE,
  PROPERTY_NAME_CREATION_DATE,
  PROPERTY_NAME_OFFSET,
  PROPERTY_NAME_DISK_NUMBER_START,
  PROPERTY_NAME_DISK_NUMBER_START,
  PROPERTY_NAME_INTERNAL_FILE_ATTRIBUTE,
  PROPERTY_NAME_INTERNAL_FILE_ATTRIBUTES,
  PROPERTY_NAME_EXTERNAL_FILE_ATTRIBUTE,
  PROPERTY_NAME_EXTERNAL_FILE_ATTRIBUTES,
  PROPERTY_NAME_MS_DOS_COMPATIBLE,
  PROPERTY_NAME_ZIP64,
  PROPERTY_NAME_ENCRYPTED,
  PROPERTY_NAME_VERSION,
  PROPERTY_NAME_VERSION_MADE_BY,
  PROPERTY_NAME_ZIPCRYPTO,
  PROPERTY_NAME_DIRECTORY,
  PROPERTY_NAME_EXECUTABLE,
  "bitFlag",
  "signature",
  "filenameUTF8",
  "commentUTF8",
  "compressionMethod",
  "extraField",
  "rawExtraField",
  "extraFieldZip64",
  "extraFieldUnicodePath",
  "extraFieldUnicodeComment",
  "extraFieldAES",
  "extraFieldNTFS",
  "extraFieldExtendedTimestamp"
];
var Entry = class {
  constructor(data) {
    PROPERTY_NAMES.forEach((name) => this[name] = data[name]);
  }
};

// node_modules/@zip.js/zip.js/lib/core/zip-reader.js
var ERR_BAD_FORMAT = "File format is not recognized";
var ERR_EOCDR_NOT_FOUND = "End of central directory not found";
var ERR_EOCDR_LOCATOR_ZIP64_NOT_FOUND = "End of Zip64 central directory locator not found";
var ERR_CENTRAL_DIRECTORY_NOT_FOUND = "Central directory header not found";
var ERR_LOCAL_FILE_HEADER_NOT_FOUND = "Local file header not found";
var ERR_EXTRAFIELD_ZIP64_NOT_FOUND = "Zip64 extra field not found";
var ERR_ENCRYPTED = "File contains encrypted entry";
var ERR_UNSUPPORTED_ENCRYPTION = "Encryption method not supported";
var ERR_UNSUPPORTED_COMPRESSION = "Compression method not supported";
var ERR_SPLIT_ZIP_FILE = "Split zip file";
var CHARSET_UTF8 = "utf-8";
var CHARSET_CP437 = "cp437";
var ZIP64_PROPERTIES = [
  [PROPERTY_NAME_UNCOMPPRESSED_SIZE, MAX_32_BITS],
  [PROPERTY_NAME_COMPPRESSED_SIZE, MAX_32_BITS],
  [PROPERTY_NAME_OFFSET, MAX_32_BITS],
  [PROPERTY_NAME_DISK_NUMBER_START, MAX_16_BITS]
];
var ZIP64_EXTRACTION = {
  [MAX_16_BITS]: {
    getValue: getUint32,
    bytes: 4
  },
  [MAX_32_BITS]: {
    getValue: getBigUint64,
    bytes: 8
  }
};
var ZipReader = class {
  constructor(reader, options = {}) {
    Object.assign(this, {
      reader: initReader(reader),
      options,
      config: getConfiguration()
    });
  }
  async *getEntriesGenerator(options = {}) {
    const zipReader = this;
    let { reader } = zipReader;
    const { config: config2 } = zipReader;
    await initStream(reader);
    if (reader.size === UNDEFINED_VALUE || !reader.readUint8Array) {
      reader = new BlobReader(await new Response(reader.readable).blob());
      await initStream(reader);
    }
    if (reader.size < END_OF_CENTRAL_DIR_LENGTH) {
      throw new Error(ERR_BAD_FORMAT);
    }
    reader.chunkSize = getChunkSize(config2);
    const endOfDirectoryInfo = await seekSignature(reader, END_OF_CENTRAL_DIR_SIGNATURE, reader.size, END_OF_CENTRAL_DIR_LENGTH, MAX_16_BITS * 16);
    if (!endOfDirectoryInfo) {
      const signatureArray = await readUint8Array(reader, 0, 4);
      const signatureView = getDataView(signatureArray);
      if (getUint32(signatureView) == SPLIT_ZIP_FILE_SIGNATURE) {
        throw new Error(ERR_SPLIT_ZIP_FILE);
      } else {
        throw new Error(ERR_EOCDR_NOT_FOUND);
      }
    }
    const endOfDirectoryView = getDataView(endOfDirectoryInfo);
    let directoryDataLength = getUint32(endOfDirectoryView, 12);
    let directoryDataOffset = getUint32(endOfDirectoryView, 16);
    const commentOffset = endOfDirectoryInfo.offset;
    const commentLength = getUint16(endOfDirectoryView, 20);
    const appendedDataOffset = commentOffset + END_OF_CENTRAL_DIR_LENGTH + commentLength;
    let lastDiskNumber = getUint16(endOfDirectoryView, 4);
    const expectedLastDiskNumber = reader.lastDiskNumber || 0;
    let diskNumber = getUint16(endOfDirectoryView, 6);
    let filesLength = getUint16(endOfDirectoryView, 8);
    let prependedDataLength = 0;
    let startOffset = 0;
    if (directoryDataOffset == MAX_32_BITS || directoryDataLength == MAX_32_BITS || filesLength == MAX_16_BITS || diskNumber == MAX_16_BITS) {
      const endOfDirectoryLocatorArray = await readUint8Array(reader, endOfDirectoryInfo.offset - ZIP64_END_OF_CENTRAL_DIR_LOCATOR_LENGTH, ZIP64_END_OF_CENTRAL_DIR_LOCATOR_LENGTH);
      const endOfDirectoryLocatorView = getDataView(endOfDirectoryLocatorArray);
      if (getUint32(endOfDirectoryLocatorView, 0) == ZIP64_END_OF_CENTRAL_DIR_LOCATOR_SIGNATURE) {
        directoryDataOffset = getBigUint64(endOfDirectoryLocatorView, 8);
        let endOfDirectoryArray = await readUint8Array(reader, directoryDataOffset, ZIP64_END_OF_CENTRAL_DIR_LENGTH, -1);
        let endOfDirectoryView2 = getDataView(endOfDirectoryArray);
        const expectedDirectoryDataOffset = endOfDirectoryInfo.offset - ZIP64_END_OF_CENTRAL_DIR_LOCATOR_LENGTH - ZIP64_END_OF_CENTRAL_DIR_LENGTH;
        if (getUint32(endOfDirectoryView2, 0) != ZIP64_END_OF_CENTRAL_DIR_SIGNATURE && directoryDataOffset != expectedDirectoryDataOffset) {
          const originalDirectoryDataOffset = directoryDataOffset;
          directoryDataOffset = expectedDirectoryDataOffset;
          prependedDataLength = directoryDataOffset - originalDirectoryDataOffset;
          endOfDirectoryArray = await readUint8Array(reader, directoryDataOffset, ZIP64_END_OF_CENTRAL_DIR_LENGTH, -1);
          endOfDirectoryView2 = getDataView(endOfDirectoryArray);
        }
        if (getUint32(endOfDirectoryView2, 0) != ZIP64_END_OF_CENTRAL_DIR_SIGNATURE) {
          throw new Error(ERR_EOCDR_LOCATOR_ZIP64_NOT_FOUND);
        }
        if (lastDiskNumber == MAX_16_BITS) {
          lastDiskNumber = getUint32(endOfDirectoryView2, 16);
        }
        if (diskNumber == MAX_16_BITS) {
          diskNumber = getUint32(endOfDirectoryView2, 20);
        }
        if (filesLength == MAX_16_BITS) {
          filesLength = getBigUint64(endOfDirectoryView2, 32);
        }
        if (directoryDataLength == MAX_32_BITS) {
          directoryDataLength = getBigUint64(endOfDirectoryView2, 40);
        }
        directoryDataOffset -= directoryDataLength;
      }
    }
    if (directoryDataOffset >= reader.size) {
      prependedDataLength = reader.size - directoryDataOffset - directoryDataLength - END_OF_CENTRAL_DIR_LENGTH;
      directoryDataOffset = reader.size - directoryDataLength - END_OF_CENTRAL_DIR_LENGTH;
    }
    if (expectedLastDiskNumber != lastDiskNumber) {
      throw new Error(ERR_SPLIT_ZIP_FILE);
    }
    if (directoryDataOffset < 0) {
      throw new Error(ERR_BAD_FORMAT);
    }
    let offset = 0;
    let directoryArray = await readUint8Array(reader, directoryDataOffset, directoryDataLength, diskNumber);
    let directoryView = getDataView(directoryArray);
    if (directoryDataLength) {
      const expectedDirectoryDataOffset = endOfDirectoryInfo.offset - directoryDataLength;
      if (getUint32(directoryView, offset) != CENTRAL_FILE_HEADER_SIGNATURE && directoryDataOffset != expectedDirectoryDataOffset) {
        const originalDirectoryDataOffset = directoryDataOffset;
        directoryDataOffset = expectedDirectoryDataOffset;
        prependedDataLength += directoryDataOffset - originalDirectoryDataOffset;
        directoryArray = await readUint8Array(reader, directoryDataOffset, directoryDataLength, diskNumber);
        directoryView = getDataView(directoryArray);
      }
    }
    const expectedDirectoryDataLength = endOfDirectoryInfo.offset - directoryDataOffset - (reader.lastDiskOffset || 0);
    if (directoryDataLength != expectedDirectoryDataLength && expectedDirectoryDataLength >= 0) {
      directoryDataLength = expectedDirectoryDataLength;
      directoryArray = await readUint8Array(reader, directoryDataOffset, directoryDataLength, diskNumber);
      directoryView = getDataView(directoryArray);
    }
    if (directoryDataOffset < 0 || directoryDataOffset >= reader.size) {
      throw new Error(ERR_BAD_FORMAT);
    }
    const filenameEncoding = getOptionValue(zipReader, options, "filenameEncoding");
    const commentEncoding = getOptionValue(zipReader, options, "commentEncoding");
    for (let indexFile = 0; indexFile < filesLength; indexFile++) {
      const fileEntry = new ZipEntry(reader, config2, zipReader.options);
      if (getUint32(directoryView, offset) != CENTRAL_FILE_HEADER_SIGNATURE) {
        throw new Error(ERR_CENTRAL_DIRECTORY_NOT_FOUND);
      }
      readCommonHeader(fileEntry, directoryView, offset + 6);
      const languageEncodingFlag = Boolean(fileEntry.bitFlag.languageEncodingFlag);
      const filenameOffset = offset + 46;
      const extraFieldOffset = filenameOffset + fileEntry.filenameLength;
      const commentOffset2 = extraFieldOffset + fileEntry.extraFieldLength;
      const versionMadeBy = getUint16(directoryView, offset + 4);
      const msDosCompatible = versionMadeBy >> 8 == 0;
      const unixCompatible = versionMadeBy >> 8 == 3;
      const rawFilename = directoryArray.subarray(filenameOffset, extraFieldOffset);
      const commentLength2 = getUint16(directoryView, offset + 32);
      const endOffset = commentOffset2 + commentLength2;
      const rawComment = directoryArray.subarray(commentOffset2, endOffset);
      const filenameUTF8 = languageEncodingFlag;
      const commentUTF8 = languageEncodingFlag;
      const externalFileAttributes = getUint32(directoryView, offset + 38);
      const directory = msDosCompatible && (getUint8(directoryView, offset + 38) & FILE_ATTR_MSDOS_DIR_MASK) == FILE_ATTR_MSDOS_DIR_MASK || unixCompatible && (externalFileAttributes >> 16 & FILE_ATTR_UNIX_DIR_MASK) == FILE_ATTR_UNIX_DIR_MASK || rawFilename.length && rawFilename[rawFilename.length - 1] == DIRECTORY_SIGNATURE.charCodeAt(0);
      const executable = unixCompatible && (externalFileAttributes >> 16 & FILE_ATTR_UNIX_EXECUTABLE_MASK) == FILE_ATTR_UNIX_EXECUTABLE_MASK;
      const offsetFileEntry = getUint32(directoryView, offset + 42) + prependedDataLength;
      Object.assign(fileEntry, {
        versionMadeBy,
        msDosCompatible,
        compressedSize: 0,
        uncompressedSize: 0,
        commentLength: commentLength2,
        directory,
        offset: offsetFileEntry,
        diskNumberStart: getUint16(directoryView, offset + 34),
        internalFileAttributes: getUint16(directoryView, offset + 36),
        externalFileAttributes,
        rawFilename,
        filenameUTF8,
        commentUTF8,
        rawExtraField: directoryArray.subarray(extraFieldOffset, commentOffset2),
        executable
      });
      fileEntry.internalFileAttribute = fileEntry.internalFileAttributes;
      fileEntry.externalFileAttribute = fileEntry.externalFileAttributes;
      const decode = getOptionValue(zipReader, options, "decodeText") || decodeText;
      const rawFilenameEncoding = filenameUTF8 ? CHARSET_UTF8 : filenameEncoding || CHARSET_CP437;
      const rawCommentEncoding = commentUTF8 ? CHARSET_UTF8 : commentEncoding || CHARSET_CP437;
      let filename = decode(rawFilename, rawFilenameEncoding);
      if (filename === UNDEFINED_VALUE) {
        filename = decodeText(rawFilename, rawFilenameEncoding);
      }
      let comment = decode(rawComment, rawCommentEncoding);
      if (comment === UNDEFINED_VALUE) {
        comment = decodeText(rawComment, rawCommentEncoding);
      }
      Object.assign(fileEntry, {
        rawComment,
        filename,
        comment,
        directory: directory || filename.endsWith(DIRECTORY_SIGNATURE)
      });
      startOffset = Math.max(offsetFileEntry, startOffset);
      readCommonFooter(fileEntry, fileEntry, directoryView, offset + 6);
      fileEntry.zipCrypto = fileEntry.encrypted && !fileEntry.extraFieldAES;
      const entry = new Entry(fileEntry);
      entry.getData = (writer, options2) => fileEntry.getData(writer, entry, options2);
      offset = endOffset;
      const { onprogress } = options;
      if (onprogress) {
        try {
          await onprogress(indexFile + 1, filesLength, new Entry(fileEntry));
        } catch (_) {
        }
      }
      yield entry;
    }
    const extractPrependedData = getOptionValue(zipReader, options, "extractPrependedData");
    const extractAppendedData = getOptionValue(zipReader, options, "extractAppendedData");
    if (extractPrependedData) {
      zipReader.prependedData = startOffset > 0 ? await readUint8Array(reader, 0, startOffset) : new Uint8Array();
    }
    zipReader.comment = commentLength ? await readUint8Array(reader, commentOffset + END_OF_CENTRAL_DIR_LENGTH, commentLength) : new Uint8Array();
    if (extractAppendedData) {
      zipReader.appendedData = appendedDataOffset < reader.size ? await readUint8Array(reader, appendedDataOffset, reader.size - appendedDataOffset) : new Uint8Array();
    }
    return true;
  }
  async getEntries(options = {}) {
    const entries = [];
    for await (const entry of this.getEntriesGenerator(options)) {
      entries.push(entry);
    }
    return entries;
  }
  async close() {
  }
};
var ZipEntry = class {
  constructor(reader, config2, options) {
    Object.assign(this, {
      reader,
      config: config2,
      options
    });
  }
  async getData(writer, fileEntry, options = {}) {
    const zipEntry = this;
    const {
      reader,
      offset,
      diskNumberStart,
      extraFieldAES,
      compressionMethod,
      config: config2,
      bitFlag,
      signature,
      rawLastModDate,
      uncompressedSize,
      compressedSize
    } = zipEntry;
    const localDirectory = fileEntry.localDirectory = {};
    const dataArray = await readUint8Array(reader, offset, 30, diskNumberStart);
    const dataView = getDataView(dataArray);
    let password = getOptionValue(zipEntry, options, "password");
    let rawPassword = getOptionValue(zipEntry, options, "rawPassword");
    const passThrough = getOptionValue(zipEntry, options, "passThrough");
    password = password && password.length && password;
    rawPassword = rawPassword && rawPassword.length && rawPassword;
    if (extraFieldAES) {
      if (extraFieldAES.originalCompressionMethod != COMPRESSION_METHOD_AES) {
        throw new Error(ERR_UNSUPPORTED_COMPRESSION);
      }
    }
    if (compressionMethod != COMPRESSION_METHOD_STORE && compressionMethod != COMPRESSION_METHOD_DEFLATE && !passThrough) {
      throw new Error(ERR_UNSUPPORTED_COMPRESSION);
    }
    if (getUint32(dataView, 0) != LOCAL_FILE_HEADER_SIGNATURE) {
      throw new Error(ERR_LOCAL_FILE_HEADER_NOT_FOUND);
    }
    readCommonHeader(localDirectory, dataView, 4);
    localDirectory.rawExtraField = localDirectory.extraFieldLength ? await readUint8Array(reader, offset + 30 + localDirectory.filenameLength, localDirectory.extraFieldLength, diskNumberStart) : new Uint8Array();
    readCommonFooter(zipEntry, localDirectory, dataView, 4, true);
    Object.assign(fileEntry, {
      lastAccessDate: localDirectory.lastAccessDate,
      creationDate: localDirectory.creationDate
    });
    const encrypted = zipEntry.encrypted && localDirectory.encrypted && !passThrough;
    const zipCrypto = encrypted && !extraFieldAES;
    if (!passThrough) {
      fileEntry.zipCrypto = zipCrypto;
    }
    if (encrypted) {
      if (!zipCrypto && extraFieldAES.strength === UNDEFINED_VALUE) {
        throw new Error(ERR_UNSUPPORTED_ENCRYPTION);
      } else if (!password && !rawPassword) {
        throw new Error(ERR_ENCRYPTED);
      }
    }
    const dataOffset = offset + 30 + localDirectory.filenameLength + localDirectory.extraFieldLength;
    const size = compressedSize;
    const readable = reader.readable;
    Object.assign(readable, {
      diskNumberStart,
      offset: dataOffset,
      size
    });
    const signal = getOptionValue(zipEntry, options, "signal");
    const checkPasswordOnly = getOptionValue(zipEntry, options, "checkPasswordOnly");
    if (checkPasswordOnly) {
      writer = new WritableStream();
    }
    writer = initWriter(writer);
    await initStream(writer, passThrough ? compressedSize : uncompressedSize);
    const { writable } = writer;
    const { onstart, onprogress, onend } = options;
    const workerOptions = {
      options: {
        codecType: CODEC_INFLATE,
        password,
        rawPassword,
        zipCrypto,
        encryptionStrength: extraFieldAES && extraFieldAES.strength,
        signed: getOptionValue(zipEntry, options, "checkSignature") && !passThrough,
        passwordVerification: zipCrypto && (bitFlag.dataDescriptor ? rawLastModDate >>> 8 & 255 : signature >>> 24 & 255),
        signature,
        compressed: compressionMethod != 0 && !passThrough,
        encrypted: zipEntry.encrypted && !passThrough,
        useWebWorkers: getOptionValue(zipEntry, options, "useWebWorkers"),
        useCompressionStream: getOptionValue(zipEntry, options, "useCompressionStream"),
        transferStreams: getOptionValue(zipEntry, options, "transferStreams"),
        checkPasswordOnly
      },
      config: config2,
      streamOptions: { signal, size, onstart, onprogress, onend }
    };
    let outputSize = 0;
    try {
      ({ outputSize } = await runWorker2({ readable, writable }, workerOptions));
    } catch (error) {
      if (!checkPasswordOnly || error.message != ERR_ABORT_CHECK_PASSWORD) {
        throw error;
      }
    } finally {
      const preventClose = getOptionValue(zipEntry, options, "preventClose");
      writable.size += outputSize;
      if (!preventClose && !writable.locked) {
        await writable.getWriter().close();
      }
    }
    return checkPasswordOnly ? UNDEFINED_VALUE : writer.getData ? writer.getData() : writable;
  }
};
function readCommonHeader(directory, dataView, offset) {
  const rawBitFlag = directory.rawBitFlag = getUint16(dataView, offset + 2);
  const encrypted = (rawBitFlag & BITFLAG_ENCRYPTED) == BITFLAG_ENCRYPTED;
  const rawLastModDate = getUint32(dataView, offset + 6);
  Object.assign(directory, {
    encrypted,
    version: getUint16(dataView, offset),
    bitFlag: {
      level: (rawBitFlag & BITFLAG_LEVEL) >> 1,
      dataDescriptor: (rawBitFlag & BITFLAG_DATA_DESCRIPTOR) == BITFLAG_DATA_DESCRIPTOR,
      languageEncodingFlag: (rawBitFlag & BITFLAG_LANG_ENCODING_FLAG) == BITFLAG_LANG_ENCODING_FLAG
    },
    rawLastModDate,
    lastModDate: getDate(rawLastModDate),
    filenameLength: getUint16(dataView, offset + 22),
    extraFieldLength: getUint16(dataView, offset + 24)
  });
}
function readCommonFooter(fileEntry, directory, dataView, offset, localDirectory) {
  const { rawExtraField } = directory;
  const extraField = directory.extraField = /* @__PURE__ */ new Map();
  const rawExtraFieldView = getDataView(new Uint8Array(rawExtraField));
  let offsetExtraField = 0;
  try {
    while (offsetExtraField < rawExtraField.length) {
      const type = getUint16(rawExtraFieldView, offsetExtraField);
      const size = getUint16(rawExtraFieldView, offsetExtraField + 2);
      extraField.set(type, {
        type,
        data: rawExtraField.slice(offsetExtraField + 4, offsetExtraField + 4 + size)
      });
      offsetExtraField += 4 + size;
    }
  } catch (_) {
  }
  const compressionMethod = getUint16(dataView, offset + 4);
  Object.assign(directory, {
    signature: getUint32(dataView, offset + 10),
    uncompressedSize: getUint32(dataView, offset + 18),
    compressedSize: getUint32(dataView, offset + 14)
  });
  const extraFieldZip64 = extraField.get(EXTRAFIELD_TYPE_ZIP64);
  if (extraFieldZip64) {
    readExtraFieldZip64(extraFieldZip64, directory);
    directory.extraFieldZip64 = extraFieldZip64;
  }
  const extraFieldUnicodePath = extraField.get(EXTRAFIELD_TYPE_UNICODE_PATH);
  if (extraFieldUnicodePath) {
    readExtraFieldUnicode(extraFieldUnicodePath, PROPERTY_NAME_FILENAME, PROPERTY_NAME_RAW_FILENAME, directory, fileEntry);
    directory.extraFieldUnicodePath = extraFieldUnicodePath;
  }
  const extraFieldUnicodeComment = extraField.get(EXTRAFIELD_TYPE_UNICODE_COMMENT);
  if (extraFieldUnicodeComment) {
    readExtraFieldUnicode(extraFieldUnicodeComment, PROPERTY_NAME_COMMENT, PROPERTY_NAME_RAW_COMMENT, directory, fileEntry);
    directory.extraFieldUnicodeComment = extraFieldUnicodeComment;
  }
  const extraFieldAES = extraField.get(EXTRAFIELD_TYPE_AES);
  if (extraFieldAES) {
    readExtraFieldAES(extraFieldAES, directory, compressionMethod);
    directory.extraFieldAES = extraFieldAES;
  } else {
    directory.compressionMethod = compressionMethod;
  }
  const extraFieldNTFS = extraField.get(EXTRAFIELD_TYPE_NTFS);
  if (extraFieldNTFS) {
    readExtraFieldNTFS(extraFieldNTFS, directory);
    directory.extraFieldNTFS = extraFieldNTFS;
  }
  const extraFieldExtendedTimestamp = extraField.get(EXTRAFIELD_TYPE_EXTENDED_TIMESTAMP);
  if (extraFieldExtendedTimestamp) {
    readExtraFieldExtendedTimestamp(extraFieldExtendedTimestamp, directory, localDirectory);
    directory.extraFieldExtendedTimestamp = extraFieldExtendedTimestamp;
  }
  const extraFieldUSDZ = extraField.get(EXTRAFIELD_TYPE_USDZ);
  if (extraFieldUSDZ) {
    directory.extraFieldUSDZ = extraFieldUSDZ;
  }
}
function readExtraFieldZip64(extraFieldZip64, directory) {
  directory.zip64 = true;
  const extraFieldView = getDataView(extraFieldZip64.data);
  const missingProperties = ZIP64_PROPERTIES.filter(([propertyName, max]) => directory[propertyName] == max);
  for (let indexMissingProperty = 0, offset = 0; indexMissingProperty < missingProperties.length; indexMissingProperty++) {
    const [propertyName, max] = missingProperties[indexMissingProperty];
    if (directory[propertyName] == max) {
      const extraction = ZIP64_EXTRACTION[max];
      directory[propertyName] = extraFieldZip64[propertyName] = extraction.getValue(extraFieldView, offset);
      offset += extraction.bytes;
    } else if (extraFieldZip64[propertyName]) {
      throw new Error(ERR_EXTRAFIELD_ZIP64_NOT_FOUND);
    }
  }
}
function readExtraFieldUnicode(extraFieldUnicode, propertyName, rawPropertyName, directory, fileEntry) {
  const extraFieldView = getDataView(extraFieldUnicode.data);
  const crc32 = new Crc32();
  crc32.append(fileEntry[rawPropertyName]);
  const dataViewSignature = getDataView(new Uint8Array(4));
  dataViewSignature.setUint32(0, crc32.get(), true);
  const signature = getUint32(extraFieldView, 1);
  Object.assign(extraFieldUnicode, {
    version: getUint8(extraFieldView, 0),
    [propertyName]: decodeText(extraFieldUnicode.data.subarray(5)),
    valid: !fileEntry.bitFlag.languageEncodingFlag && signature == getUint32(dataViewSignature, 0)
  });
  if (extraFieldUnicode.valid) {
    directory[propertyName] = extraFieldUnicode[propertyName];
    directory[propertyName + "UTF8"] = true;
  }
}
function readExtraFieldAES(extraFieldAES, directory, compressionMethod) {
  const extraFieldView = getDataView(extraFieldAES.data);
  const strength = getUint8(extraFieldView, 4);
  Object.assign(extraFieldAES, {
    vendorVersion: getUint8(extraFieldView, 0),
    vendorId: getUint8(extraFieldView, 2),
    strength,
    originalCompressionMethod: compressionMethod,
    compressionMethod: getUint16(extraFieldView, 5)
  });
  directory.compressionMethod = extraFieldAES.compressionMethod;
}
function readExtraFieldNTFS(extraFieldNTFS, directory) {
  const extraFieldView = getDataView(extraFieldNTFS.data);
  let offsetExtraField = 4;
  let tag1Data;
  try {
    while (offsetExtraField < extraFieldNTFS.data.length && !tag1Data) {
      const tagValue = getUint16(extraFieldView, offsetExtraField);
      const attributeSize = getUint16(extraFieldView, offsetExtraField + 2);
      if (tagValue == EXTRAFIELD_TYPE_NTFS_TAG1) {
        tag1Data = extraFieldNTFS.data.slice(offsetExtraField + 4, offsetExtraField + 4 + attributeSize);
      }
      offsetExtraField += 4 + attributeSize;
    }
  } catch (_) {
  }
  try {
    if (tag1Data && tag1Data.length == 24) {
      const tag1View = getDataView(tag1Data);
      const rawLastModDate = tag1View.getBigUint64(0, true);
      const rawLastAccessDate = tag1View.getBigUint64(8, true);
      const rawCreationDate = tag1View.getBigUint64(16, true);
      Object.assign(extraFieldNTFS, {
        rawLastModDate,
        rawLastAccessDate,
        rawCreationDate
      });
      const lastModDate = getDateNTFS(rawLastModDate);
      const lastAccessDate = getDateNTFS(rawLastAccessDate);
      const creationDate = getDateNTFS(rawCreationDate);
      const extraFieldData = { lastModDate, lastAccessDate, creationDate };
      Object.assign(extraFieldNTFS, extraFieldData);
      Object.assign(directory, extraFieldData);
    }
  } catch (_) {
  }
}
function readExtraFieldExtendedTimestamp(extraFieldExtendedTimestamp, directory, localDirectory) {
  const extraFieldView = getDataView(extraFieldExtendedTimestamp.data);
  const flags = getUint8(extraFieldView, 0);
  const timeProperties = [];
  const timeRawProperties = [];
  if (localDirectory) {
    if ((flags & 1) == 1) {
      timeProperties.push(PROPERTY_NAME_LAST_MODIFICATION_DATE);
      timeRawProperties.push(PROPERTY_NAME_RAW_LAST_MODIFICATION_DATE);
    }
    if ((flags & 2) == 2) {
      timeProperties.push(PROPERTY_NAME_LAST_ACCESS_DATE);
      timeRawProperties.push(PROPERTY_NAME_RAW_LAST_ACCESS_DATE);
    }
    if ((flags & 4) == 4) {
      timeProperties.push(PROPERTY_NAME_CREATION_DATE);
      timeRawProperties.push(PROPERTY_NAME_RAW_CREATION_DATE);
    }
  } else if (extraFieldExtendedTimestamp.data.length >= 5) {
    timeProperties.push(PROPERTY_NAME_LAST_MODIFICATION_DATE);
    timeRawProperties.push(PROPERTY_NAME_RAW_LAST_MODIFICATION_DATE);
  }
  let offset = 1;
  timeProperties.forEach((propertyName, indexProperty) => {
    if (extraFieldExtendedTimestamp.data.length >= offset + 4) {
      const time = getUint32(extraFieldView, offset);
      directory[propertyName] = extraFieldExtendedTimestamp[propertyName] = new Date(time * 1e3);
      const rawPropertyName = timeRawProperties[indexProperty];
      extraFieldExtendedTimestamp[rawPropertyName] = time;
    }
    offset += 4;
  });
}
async function seekSignature(reader, signature, startOffset, minimumBytes, maximumLength) {
  const signatureArray = new Uint8Array(4);
  const signatureView = getDataView(signatureArray);
  setUint32(signatureView, 0, signature);
  const maximumBytes = minimumBytes + maximumLength;
  return await seek(minimumBytes) || await seek(Math.min(maximumBytes, startOffset));
  async function seek(length) {
    const offset = startOffset - length;
    const bytes = await readUint8Array(reader, offset, length);
    for (let indexByte = bytes.length - minimumBytes; indexByte >= 0; indexByte--) {
      if (bytes[indexByte] == signatureArray[0] && bytes[indexByte + 1] == signatureArray[1] && bytes[indexByte + 2] == signatureArray[2] && bytes[indexByte + 3] == signatureArray[3]) {
        return {
          offset: offset + indexByte,
          buffer: bytes.slice(indexByte, indexByte + minimumBytes).buffer
        };
      }
    }
  }
}
function getOptionValue(zipReader, options, name) {
  return options[name] === UNDEFINED_VALUE ? zipReader.options[name] : options[name];
}
function getDate(timeRaw) {
  const date = (timeRaw & 4294901760) >> 16, time = timeRaw & 65535;
  try {
    return new Date(1980 + ((date & 65024) >> 9), ((date & 480) >> 5) - 1, date & 31, (time & 63488) >> 11, (time & 2016) >> 5, (time & 31) * 2, 0);
  } catch (_) {
  }
}
function getDateNTFS(timeRaw) {
  return new Date(Number(timeRaw / BigInt(1e4) - BigInt(116444736e5)));
}
function getUint8(view, offset) {
  return view.getUint8(offset);
}
function getUint16(view, offset) {
  return view.getUint16(offset, true);
}
function getUint32(view, offset) {
  return view.getUint32(offset, true);
}
function getBigUint64(view, offset) {
  return Number(view.getBigUint64(offset, true));
}
function setUint32(view, offset, value) {
  view.setUint32(offset, value, true);
}
function getDataView(array) {
  return new DataView(array.buffer);
}

// node_modules/@zip.js/zip.js/lib/core/zip-writer.js
var EXTRAFIELD_DATA_AES = new Uint8Array([7, 0, 2, 0, 65, 69, 3, 0, 0]);

// node_modules/@zip.js/zip.js/lib/zip-fs.js
var baseURL;
try {
  baseURL = import.meta.url;
} catch (_) {
}
configure({ baseURL });
e(configure);

// node_modules/@zip.js/zip.js/index.js
configure({ Deflate: ZipDeflate, Inflate: ZipInflate });

// src/InfoLiteEntryTypes.json
var InfoLiteEntryTypes_default = {
  MASTERDB: {
    type: "Master Database",
    id: 0,
    icon: "data:image/png;base64,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"
  },
  TRANSPORTDB: {
    type: "Transportable Database",
    id: 0,
    icon: "data:image/png;base64,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"
  },
  RECYCLEBIN: {
    type: "Recycle Bin",
    id: -1,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPz8/AT8/PwE/Pz8BPz8/AT8/PwE/Pz8BAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8/PwE/Pz8QPz8/ET8/Pyg/Pz8zPz8/Mz8/PzM/Pz8zPz8/Mz8/Pys/Pz8SPz8/ET8/PwkAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD8/PwE/Pz8XPz8/SD8/P1o/Pz9tPz8/gT8/P4E/Pz+BPz8/gT8/P4E/Pz98Pz8/Xj8/P1o/Pz9UPz8/Nj8/Pxs/Pz8JAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/Pz8CPz8/Qj8/P40/Pz+nPz8/tT8/P84/Pz/OPz8/zj8/P84/Pz/OPz8/zD8/P68/Pz+oPz8/pD8/P4Y/Pz9tPz8/VD8/Py4/Pz8KAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAPz8/AT8/P1xxbWvampOQ952YlPj99u7////4/////P//+/L/+vLq//Tp4v/DuLP9lYuJ+JOHhfg/Pz/XPz8/wD8/P6Q/Pz+CPz8/WD8/Py4/Pz8CAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACbjYxwvq6r9+va1f/y5N7/9+3m//327v////j////8///78v/68ur/9Oni/+7f2f/o1dH/48zJ/9zCwP+NfX34Pz8/1T8/P6w/Pz+CPz8/QD8/PwIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAtqGfU9/HxP/m0c3/69rV//Lk3v/37eb//fbu////+P////z///vy//ry6v/06eL/7t/Z/+jV0f/jzMn/3MLA/9e5uP+skpL9Pz8/1T8/P5o/Pz9APz8/AgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADavbz/38fE/+bRzf/r2tX/8uTe//ft5v/99u7////4/////P//+/L/+vLq//Tp4v/u39n/6NXR/+PMyf/cwsD/17m4/9KwsP+KeHj3Pz8/mz8/P0A/Pz8CAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAANq9vP/fx8T/5tHN/+va1f/y5N7/9+3m//327v////j////8///78v/68ur/9Oni/+7f2f/o1dH/48zJ/9zCwP/Xubj/0rCw/4p4ePc/Pz+bPz8/QD8/PwIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA2r28/9/HxP/m0c3/69rV//Lk3v/37eb//fbu////+P////z///vy//ry6v/06eL/7t/Z/+jV0f/jzMn/3MLA/9e5uP/SsLD/inh49z8/P5s/Pz9APz8/AgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADavbz/38fE/+bRzf/r2tX/8uTe///////////////////////9//T/////////////////+uzp/+PMyf/cwsD/17m4/9KwsP+KeHj3Pz8/mz8/P0A/Pz8CAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAANq9vP/fx8T/5tHN/+va1f////////////////+7/6n/aP9L/3f/XP97/2D/////////////////48zJ/9zCwP/Xubj/0rCw/4p4ePc/Pz+bPz8/QD8/PwIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA2r28/9/HxP/m0c3/69rV//////////////////f/7f///////////+7/4///////7v/j///////jzMn/3MLA/9e5uP/SsLD/inh49z8/P5s/Pz9APz8/AgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADavbz/38fE/+bRzf/r2tX///////////+V/37///////////////////////////9c/z3//////+PMyf/cwsD/17m4/9KwsP+KeHj3Pz8/mz8/P0A/Pz8CAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAANq9vP/fx8T/5tHN/+va1f///////////1v/PP////r/6P/c//b/7f//////9f/r/3H/Vf/z/+r/48zJ/9zCwP/Xubj/0rCw/4p4ePc/Pz+bPz8/QD8/PwIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA2r28/9/HxP/m0c3/69rV////////////Tv8t/3f/XP+q/5X/xf+0//////+d/4j/vf+s///////jzMn/3MLA/9e5uP/SsLD/inh49z8/P5s/Pz9APz8/AgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADavbz/38fE/+bRzf/r2tX//////////////////////////////////////////////////////+PMyf/cwsD/17m4/9KwsP+KeHj3Pz8/mz8/P0A/Pz8CAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAANq9vP/fx8T/5tHN/+va1f////////////////////j////8///78v/68ur/9Oni////////////48zJ/9zCwP/Xubj/0rCw/4p4ePc/Pz+bPz8/QD8/PwIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA2r28/9/HxP/m0c3/69rV//Lk3v/37eb//fbu////+P////z///vy//ry6v/06eL/7t/Z/+jV0f/jzMn/3MLA/9e5uP/SsLD/inh4+D8/P5s/Pz9APz8/AgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADavbz/38fE/+bRzf/r2tX/8uTe//ft5v/99u7////4/////P//+/L/+vLq//Tp4v/u39n/6NXR/+PMyf/cwsD/17m4/9KwsP+KeHj5Pz8/mz8/P0A/Pz8CAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAANq9vP/fx8T/5tHN/+va1f/y5N7/9+3m//327v////j////8///78v/68ur/9Oni/+7f2f/o1dH/48zJ/9zCwP/Xubj/0rCw/4l3d/o/Pz+bPz8/QD8/PwIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA2r28/9/HxP/m0c3/xrm1/46Ihf9mZGL/TEtK/z8/P/8/Pz//Pz8//z8/P/8/Pz//SklJ/2FdXP+HfXz/vKel/9e5uP/SsLD/inh49j8/P5I/Pz9APz8/AgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADVubj/mYuK/11ZWP9mZGP/tLKx/////v//////////////////////////////////////5N3c/5yTkv9RTk7/Y1tb/6eOjv+RfX3hPz8/bD8/PzY/Pz8CAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHJpaf+bmZn///39////////////9/Ht/NHMyP/Ixr//x8W//8C7tP+5r6n/w7m0/9bKx//////////////////Tzc3/bWpq/3hqats/Pz9CPz8/EgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA///////////h0M3/lnt0/5yHf/+qm5P/t66n/8TCvP++ubL/sKSd/6KQif+Wfnb/impi/3xVTP9wQzv/qIV//+3b2f//////2srKyD8/PxgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAC/nJj/iE9E/5xtYf+th3z/v6KX/9G9s//j2M7/9vPq/+3m3f/aysD/yK+k/7WUif+leW7/k19T/4FEN/9uKRv/YhUI/34+Nf+pfnrHPz8/AQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIA9L0CQVEe/o3Bk/7aNgf/IqZ7/3Me8/+/j2f////f/+fLo/+XUyv/SuK3/vpuP/6x+cv+ZYlX/hUQ3/3IoGv9kEgT/ZBIEgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACndmpAto2BgMipnoDdyL2/7+PZ////9//58uj/5dTK/9K4rf++m4//rH5y/5liVYCFRDeAcigagAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA=="
  },
  AG: {
    type: "Asset Group",
    id: 176,
    icon: "data:image/png;base64,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"
  },
  MODG: {
    type: "Model Group",
    id: 175,
    icon: "data:image/png;base64,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lf8z85D/L/ON/y7ziP8s84b/LPKC/x60Wf8TkUD6XY9oGaiFhQeIiXILkaidFhqWSsgTkkP/EKhK/w3DVf8Jylb/Cc1Y/wzRX/8P1GH/GNZr/zHYeP9X2Yn/nNON/8nPif/RzIL/z8+F/7jTi/+F2JD/Td6L/zPggf8t4H3/K998/yrfef8o3nb/Jdxz/yLWbP8bs1f/FJJC/xeRQqmnkpIMcXJyBYWFhQeJiYkLNZZXJA6PPcQJjjn/Bow3/wWMNv8Fjjb/BpA4/weTOv8JlDz/EpdB/x6aR/8vmE7/QpRR/0qTUP9GlU//O5ZO/yiZTP8am0f/E5lC/xGXQP8QlkH/D5Q+/w6SPf8Ojzz/Do88/wyQPP4PjjyxRIdVFnFxcQZqamoBampqAWpqagJqamoDampqAweLNygHizdABYw2PwWMNj8FjDY/B403QAmOOUEPjDxEGItDSiOJSVEpiUxWLIhOWSyITlkniUtUHopGThaLQUkPjDxEDY07QwyMOUIMizlCDIs5QgyLOUIJjDlAD4o7I2pqagNqamoCampqAf///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AGpqagFqamoDampqBWpqagdqamoHampqB2pqagVqamoEampqAmpqagFqamoBampqAWpqagFqamoBampqAWpqagH///8A////AP///wD///8A////AA=="
  },
  CINF: {
    type: "Collection Inference",
    id: 105,
    icon: "data:image/png;base64,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"
  },
  CNN: {
    type: "Collection Network",
    id: 134,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wD///8APj49AkI+OwVMQDcKWUIzEWNFLxhtRywfcUgrJnJIKyp0SCoudkkpL3ZJKS90SCoucUgrKnBIKyZrRi0fYkQwGFdCMxFLQDgKQT47BT4+PQL///8A////AP///wD///8A////AP///wD///8A////AP///wD///8APj4+AT4+PQw+Pj0jRT86QFxDMlt7Sidtkk8fd6FSG32qVBiBsFYWg7NWFYW0VxSFtFYUhbNWFYWvVRaDqVQYgaBSG32QTyB3d0kpbVhDM1pDPjtAPj49JT4+PQ0+Pj4C////AP///wD///8A////AP///wD///8A////AP///wA+Pj4DPj4+Ez4+PTVHPzlbZUUveoxOIoqqVBiNtlAYpq5FHsigPCXhljYq8pAyLfuQMi37lTYq8qA8JeGuRR7ItVAYpqdUGI2ITSOKYUUxekU/Ols+Pj03Pj4+FD4+PgP///8A////AP///wD///8A////AP///wD///8A////AP///wA+Pj0CPj09CUc+OhNXQDUjeT0uiI01LeeSMy3/lzgr/54/KP+kRCb/p0cl/6dHJf+kRCb/nj8o/5c4K/+SMy3/jTUt53c9LodVQDYjRz06FD49PQk+Pj0C////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AejUyI4syL8eUNC3/nj0p/65MI/+9WR3/x2MY/85oFv/RaxX/0WsV/85oFv/HYxj/vVkd/65MI/+ePSn/lDQt/4wyL8h6NTIj////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AJIxLkWTMS7wmjgr/6xJJP/AXBz/z2kW/9VvE//YcRP/2XMS/9pzEv/acxL/2XMS/9hxE//VbxP/z2kW/8BcHP+sSST/mjgr/5MxLvCTMS5F////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wCVMS5FlTIu+J46Kv+zTiL/x2EZ/9FpFf/UbBT/1G0U/9RtFP/UbRT/1G0U/9RtFP/UbRT/1G0U/9RtFP/UbBT/0WkV/8dhGf+zTiL/njoq/5UyLviVMS5F////AP///wD///8A////AP///wD///8A////AP///wD///8AlzEuJZcxLvCfOSv/skwi/8VdG//MZBj/zWUX/81lF//NZRf/zWUX/81lF//NZRf/zWUX/81lF//NZRf/zWUX/81lF//NZRf/zGQY/8VdG/+yTCL/nzkr/5cxLvCXMS4l////AP///wD///8A////AP///wD///8A////AJkxLwKZMi/HnTYt/61FJv+9Vh//xFwc/8VdHP/FXRz/xV0c/8VdHP/FXRz/xV0c/8VdHP/FXRz/xV0c/8VdHP/FXRz/xV0c/8VdHP/FXRz/xFwc/71WH/+tRSb/nTYt/5kyL8eZMS8C////AP///wD///8A////AP///wD///8AmzIvXpwzL/+mPCv/tEsk/7tSIf+8UyD/vFMg/7xTIP+8UyD/vFMg/7xTIP+8UyD/vFMg/7xTIP+8UyD/vFMg/7xTIP+8UyD/vFMg/7xTIP+8UyD/u1Ih/7RLJP+mPCv/nDMv/5syL17///8A////AP///wD///8A////AJ8yLwGeMi/XoTUu/6s/Kf+yRyb/tEgl/7RIJf+0SCX/tEgl/7RIJf+0SCX/tEgl/7RIJf+0SCX/tEgl/7RIJf+0SCX/tEgl/7RIJf+0SCX/tEgl/7RIJf+0SCX/skcm/6s/Kf+hNS7/njIv154yLwH///8A////AP///wD///8AoTIwO6EyL/+kNS7/qjwr/60+Kv+tPyr/rT8q/60/Kv+tPyr/rT8q/60/Kv+tPyr/rT8q/60/Kv+tPyr/rT8q/60/Kv+tPyr/rT8q/60/Kv+tPyr/rT8q/60/Kv+tPir/qjwr/6Q1Lv+hMi//oTIvO////wD///8A////AP///wCjMjCHpDIv/6U0Lv+nNi3/qDYt/6g2Lf+oNi3/qDYt/6g2Lf+oNi3/qDYt/6g2Lf+oNi3/qDYt/6g2Lf+oNi3/qDYt/6g2Lf+oNi3/qDYt/6g2Lf+oNi3/qDYt/6g2Lf+nNi3/pTQu/6QyL/+jMjCH////AP///wD///8A////AKYyML+nMzD/pzMv/6czL/+nMy//pzMv/6czL/+nMy//pzMv/6czL/+nMy//pzMv/6czL/+nMy//pzMv/6czL/+nMy//pzMv/6czL/+nMy//pzMv/6czL/+nMy//pzMv/6czL/+nMy//pzMw/6YyMMD///8A////AP///wD///8AqTMw5KozMP+qMzD/qjMw/6ozMP+qMzD/qjMw/6ozMP+qMzD/qjMw/6ozMP+qMzD/qjMw/6ozMP+qMzD/qjMw/6ozMP+qMzD/qjMw/6ozMP+qMzD/qjMw/6ozMP+qMzD/qjMw/6ozMP+qMzD/qTMw5P///wD///8A////AP///wCtMzH2rTMx/60zMf+tMzH/rTMx/60zMf+tMzH/rTMx/60zMf+tMzH/rTMx/60zMf+tMzH/rTMx/60zMf+tMzH/rTMx/60zMf+tMzH/rTMx/60zMf+tMzH/rTMx/60zMf+tMzH/rTMx/60zMf+tMzH2////AP///wD///8A////ALAzMfayOTf/u1BO/7tRT/+5Skj/tUE//7E1M/+wMzH/sDMx/7AzMf+wMzH/sDMx/7AzMf+wMzH/sDMx/7AzMf+wMzH/sDMx/7AzMf+wMzH/sDMx/7E2NP+1QT//uUpI/7tRT/+7UE7/sjk3/7AzMfb///8A////AP///wD///8AsjMx5LtKR//FY2D/xWNg/8VjYP/FY2D/xGJg/8FZVv+8TUr/t0E+/7M2M/+zNDH/szQx/7M0Mf+zNDH/szQx/7M0Mf+zNjP/t0A+/7xNSv/BWVb/xGJg/8VjYP/FY2D/xWNg/8VjYP+7Skf/sjMx5P///wD///8A////AP///wC1NDG/vUZE/8ppZ//KaWf/ymln/8ppZ//KaWf/ymln/8ppZ//KaWf/yWlm/8diX//EW1j/wldU/8JXVP/EW1j/x2Jf/8lpZv/KaWf/ymln/8ppZ//KaWf/ymln/8ppZ//KaWf/ymln/7xGQ/+1NDHA////AP///wD///8A////ALg0MYe7Ojf/znBu/85wbv/OcG7/znBu/85wbv/OcG7/znBu/85wbv/OcG7/znBu/85wbv/OcG7/znBu/85wbv/OcG7/znBu/85wbv/OcG7/znBu/85wbv/OcG7/znBu/85wbv/OcG7/uzo3/7g0MYf///8A////AP///wD///8AujQxO7s0Mf/NZ2b/0nd1/9J3df/Sd3X/0nd1/9J3df/Sd3X/0nd1/9J3df/Sd3X/0nd1/9J3df/Sd3X/0nd1/9J3df/Sd3X/0nd1/9J3df/Sd3X/0nd1/9J3df/Sd3X/0nd1/81nZf+7NDH/ujQxO////wD///8A////AP///wD///8AvjQy18ZNSv/Wfnz/1n58/9Z+fP/Wfnz/1n58/9Z+fP/Wfnz/1n58/9Z+fP/Wfnz/1n58/9Z+fP/Wfnz/1n58/9Z+fP/Wfnz/1n58/9Z+fP/Wfnz/1n58/9Z+fP/Wfnz/xkxK/740Mtf///8A////AP///wD///8A////AP///wDANDJewTUy/9Rzcf/ahYP/2oWD/9qFg//ahYP/2oWD/9qFg//ahYP/2oWD/9qFg//ahYP/2oWD/9qFg//ahYP/2oWD/9qFg//ahYP/2oWD/9qFg//ahYP/2oWD/9Rzcf/BNTL/wDQyXv///wD///8A////AP///wD///8A////AME1MgLDNTLHyEI//9yHhf/di4n/3YuJ/92Lif/di4n/3YuJ/92Lif/di4n/3YuJ/92Lif/di4n/3YuJ/92Lif/di4n/3YuJ/92Lif/di4n/3YuJ/92Lif/ch4X/yEI//8M1MsfCNTIC////AP///wD///8A////AP///wD///8A////AMY1MiXINTLwz1BO/+CPjv/hkY//4ZGP/+GRj//hkY//4ZGP/+GRj//hkY//4ZGP/+GRj//hkY//4ZGP/+GRj//hkY//4ZGP/+GRj//hkY//4I+O/89RTv/INTLwxjUyJf///wD///8A////AP///wD///8A////AP///wD///8A////AMk1MkTKNTL30lJP/+KSkP/klpX/5JaV/+SWlf/klpX/5JaV/+SWlf/klpX/5JaV/+SWlf/klpX/5JaV/+SWlf/klpX/5JaV/+KSkP/SUlD/yjUy+Mk1MkT///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AMs1MkTMNTLw0EVC/+CFg//mnJr/5pya/+acmv/mnJr/5pya/+acmv/mnJr/5pya/+acmv/mnJr/5pya/+acmv/ghYP/0EVC/8w1MvDLNTJF////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AM01MiPONjLHzjYy/9ZZVv/ih4X/6KCf/+ihn//ooZ//6KGf/+ihn//ooZ//6KGf/+ign//ih4X/1llW/842Mv/ONjLHzTUyI////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AM42MgLPNjJezzYz1tA2M//SQT7/2Vxa/91ta//fdnT/33Z0/91ta//ZXFr/0kE+/9A2M//PNjPWzzYyXs42MgL///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A0DYzOdA2M4fRNjO/0TYz5NE2M/bRNjP20TYz5NE2M7/QNjOH0DYzOf///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  CNTMP: {
    type: "Collection Digitisation Template",
    id: 150,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AKqmpgWqpqYwrKmpWrSxsXi9urqPvry8ocPAwK/HxcW0xsPDt8TBwb/EwcG/xsPDt8fFxbTDwcGvvry8ob26uo+1sbF4raqqWqunpzCrqKgF////AP///wD///8A////AP///wD///8A////AP///wD///8A////AKypqSC3tLSXz83N7ODb2//n4eH/5Nvb/+LW1v/g0tL/3tDQ/93Ozv/czc3/3MzM/9zMzP/czc3/3c7O/97Q0P/g0tL/4tbW/+Tb2//n4eH/4Nvb/9DNze26traZrqurJ////wD///8A////AP///wD///8A////AP///wCvq6tX1dLS9OTb2//Yxsb/076+/9K9vf/Svb3/0r29/9K9vf/Svb3/0r29/9K9vf/Svb3/0r29/9K9vf/Svb3/0r29/9K9vf/Svb3/0r29/9K9vf/Tvr7/2MbG/+Ta2v/Z1tb4s6+va////wD///8A////AP///wD///8ArqurP93a2vrczMz/1L+//9S/v//Uv7//1L+//9S/v//Uv7//1L+//9S/v//Uv7//1L+//9S/v//Uv7//1L+//9S/v//Uv7//1L+//9S/v//Uv7//1L+//9S/v//Uv7//1L+//9rJyf/h3t79sKysT////wD///8A////AKqlpQHFwsLP4NPT/9XBwf/VwcH/1cHB/9XBwf/VwcH/1cHB/9XBwf/VwcH/1cHB/9XBwf/VwcH/1cHB/9XBwf/VwcH/1cHB/9XBwf/VwcH/1cHB/9XBwf/VwcH/1cHB/9XBwf/VwcH/1cHB/9/R0f/IxcXYrqurAv///wD///8Aq6enN+Le3v7YxcX/18TE/9fExP/XxMT/18TE/9fExP/Ww8P/0b+//8e0s//Draj/xKmg/8Smm//EpZn/xKWZ/8Smm//EqaD/w62o/8e1tP/Rv7//1sPD/9fExP/XxMT/18TE/9fExP/XxMT/2MXF/+Lf3/6vq6s4////AP///wCzsLB36OHh/9nGxv/Zxsb/2cbG/9nGxv/Zxsb/2cbG/9fExP/Lurr/uKWj/7aOfv+6emP/s2pW/6xhUP+sYVD/s2pW/7p6Y/+1jn7/uKWj/8q5uf/XxMT/2cbG/9nGxv/Zxsb/2cbG/9nGxv/Zxsb/6OHh/7azs3b///8A////AL68vJ3k29v/28nJ/9vJyf/bycn/28nJ/9vJyf/bycn/28nJ/9bDw/+2kpD/qWNW/7dlRf/EcD7/y3c8/8t3O//EcD7/t2VF/6hjVv+2kpD/1sPD/9vJyf/bycn/28nJ/9vJyf/bycn/28nJ/9vJyf/l3Nz/v729m////wD///8AxMHBteTZ2f/czMz/3MzM/9zMzP/czMz/3MzM/9zMzP/Yxsb/vIqI/65dSv/Gcj7/0n06/9aAOP/WgTn/1oE4/9aAOP/SfTr/xnI+/65dSv+9ioj/2MbG/9zMzP/czMz/3MzM/9zMzP/czMz/3MzM/+TZ2f/FwsKz////AP///wDIxcXK5NjY/97Pz//ez8//3s/P/97Pz//ez8//3s/P/8OXlf+vWkz/xG9B/8x3Pv/Mdz7/zHc+/8x3Pv/Mdz7/zHc+/8x3Pv/Mdz7/xG9B/69aTP/EmJb/3s/P/97Pz//ez8//3s/P/97Pz//ez8//5NnZ/8fExMb///8A////AMvJydTj19f/39HR/9/R0f/f0dH/39HR/9/R0f/Su7v/s2Rf/7hgSP/AaUX/wWlE/8FpRP/BaUT/wWpF/8FpRP/BaUT/wWlE/8FpRP/AaUX/uGBI/7NkX//TvLz/39HR/9/R0f/f0dH/39HR/9/R0f/k2Nj/zMrK0v///wD///8AysjI4eTX1//g0dH/4NHR/+DR0f/g0dH/4NHR/8WWlf+wVU//tlpL/7dcS/+3W0v/t1tL/7dbS/+3XEv/t1tL/7dbS/+3W0v/t1tL/7dcS/+2Wkv/sFVP/8aXlf/g0dH/4NHR/+DR0f/g0dH/4NHR/+TY2P/KyMja////AP///wDMysro5NjY/+HT0//h09P/4dPT/+HT0//h09P/vXd2/7JTT/+zU0//s1RQ/7NTT/+zU0//s1NP/7NUUP+zU0//s1NP/7NTT/+zU0//s1RQ/7NTT/+yU0//vnh2/+HT0//h09P/4dPT/+HT0//h09P/5NnZ/8vIyOL///8A////AM7Ly+zk2dn/4tTU/+LU1P/i1NT/4tTU/+LU1P+7aGb/tlNR/7ZTUf+2U1H/tlNR/7ZTUf+2U1H/tlNR/7ZTUf+2U1H/tlNR/7ZTUf+2U1H/tlNR/7ZTUf+9aGf/4tTU/+LU1P/i1NT/4tTU/+LU1P/k2dn/zMnJ5v///wD///8AzszM7eTa2v/j1tb/49bW/+PW1v/j1tb/49bW/8Brav/FbGv/xXBt/8JoZ/+/YF3/vVhW/7tUUv+7VFL/u1RS/7tUUv+9WFb/v2Bd/8JoZ//FcG3/xWxr/8Jsa//j1tb/49bW/+PW1v/j1tb/49bW/+Xb2//Mycnn////AP///wDNy8vq5dvb/+TX1//k19f/5NfX/+TX1//k19f/yH18/814dv/PgH7/z4B//85+ff/OfXr/zHl2/8t0cv/KdHH/zHl2/859ev/Ofn3/z4B//8+Afv/MeHb/yX18/+TX1//k19f/5NfX/+TX1//k19f/5dzc/8vJyeT///8A////AMvJyeXm3d3/5NnZ/+TZ2f/k2dn/5NnZ/+TZ2f/RnJv/z3Z0/9WKiP/Vion/1YqI/9WKiP/Vioj/1YqJ/9WKiP/Vioj/1YqI/9WKiP/Vion/1YqI/891dP/RnZz/5NnZ/+TZ2f/k2dn/5NnZ/+TZ2f/m3t7/ycfH3f///wD///8AysjI2uff3//l2tr/5dra/+Xa2v/l2tr/5dra/9vExP/Pc3H/2ZCO/9uUkv/blJL/25SS/9uUkv/blJL/25SS/9uUkv/blJL/25SS/9uUkv/ZkI7/z3Nx/9zExP/l2tr/5dra/+Xa2v/l2tr/5dra/+fg4P/MysrU////AP///wDKyMjQ6OHh/+Xc3P/l3Nz/5dzc/+Xc3P/l3Nz/5dzc/9ehoP/UdnX/352c/9+dnP/fnZz/352c/9+dnP/fnZz/352c/9+dnP/fnZz/352c/9R2df/YoqH/5dzc/+Xc3P/l3Nz/5dzc/+Xc3P/l3Nz/6eLi/8nGxsv///8A////AMXCwr7q5OT/5t3d/+bd3f/m3d3/5t3d/+bd3f/m3d3/4tfX/9qWlP/Zenj/45+f/+SmpP/kpaT/5KWk/+SmpP/kpaT/5Kak/+Ofn//Zenj/2paV/+PX1//m3d3/5t3d/+bd3f/m3d3/5t3d/+bd3f/q5OT/xsPDuf///wD///8AwL6+qOvl5f/n3t7/597e/+fe3v/n3t7/597e/+fe3v/n3t7/5NjY/9yjov/ZeXf/34yJ/+SdnP/lo6H/5aOh/+SdnP/fjIn/2Xl3/92jov/k2Nj/597e/+fe3v/n3t7/597e/+fe3v/n3t7/597e/+zm5v/Bvr6k////AP///wC4tLSE7enp/+jf3//o39//6N/f/+jf3//o39//6N/f/+jf3//o39//6N/f/+DJyP/boqH/24WE/9t6ef/benn/24WE/9yiof/hycj/6N/f/+jf3//o39//6N/f/+jf3//o39//6N/f/+jf3//o39//7enp/7u4uIL///8A////AKypqUrp5ub/6eDg/+jg4P/o4OD/6ODg/+jg4P/o4OD/6ODg/+jg4P/o4OD/6ODg/+jg4P/o4OD/6ODg/+jg4P/o4OD/6ODg/+jg4P/o4OD/6ODg/+jg4P/o4OD/6ODg/+jg4P/o4OD/6ODg/+ng4P/p5ub/sa2tSf///wD///8Aq6ioBcvJyePr5eX/6eHh/+nh4f/p4eH/6eHh/+nh4f/p4eH/6eHh/+nh4f/p4eH/6eHh/+nh4f/p4eH/6eHh/+nh4f/p4eH/6eHh/+nh4f/p4eH/6eHh/+nh4f/p4eH/6eHh/+nh4f/p4eH/6+Tk/87MzOexra0G////AP///wD///8AsKysW+bk5P7r5OT/6uLi/+ri4v/q4uL/6uLi/+ri4v/q4uL/6uLi/+ri4v/q4uL/6uLi/+ri4v/q4uL/6uLi/+ri4v/q4uL/6uLi/+ri4v/q4uL/6uLi/+ri4v/q4uL/6uLi/+rj4//q6Oj/tLGxbP///wD///8A////AP///wD///8As7CwguLh4f3t6en/6+Tk/+rj4//q4+P/6uPj/+rj4//q4+P/6uPj/+rj4//q4+P/6uPj/+rj4//q4+P/6uPj/+rj4//q4+P/6uPj/+rj4//q4+P/6uPj/+rj4//s5ub/6efn/7m1taOxra0C////AP///wD///8A////AP///wD///8AsKysQMG+vrrZ19f77Orq/+/s7P/u6ur/7ejo/+3n5//s5ub/7Obm/+zl5f/s5eX/7OXl/+zl5f/s5eX/7Obm/+3n5//t6Oj/7unp/+/r6//v7e3/5OLi/srIyN+yr69nsa2tAv///wD///8A////AP///wD///8A////AP///wD///8A////ALCsrBavq6tOuLS0d768vJTFwsKvxsPDw8vJydHLycnbysjI4MzKyufMysrozMnJ5srHx9/MysrVycbGy8XDw7rBv7+kvbq6irSxsWawrKwyr6urAv///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  COST: {
    type: "Collection Cost Estimator",
    id: 110,
    icon: "data:image/png;base64,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"
  },
  CR: {
    type: "Custom Report",
    id: 113,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wAgHx4BFBISAhAPDwIQDw8CEA8PAhAPDwIQDw8CEA8PAhAPDwIQDw8CEA8PAhAPDwIQDw8CEA8PAhAPDwIQDw8CEA8PAhAPDwIQDw8CEA8OAg4NDQILCwoCDQwMAf///wD///8A////AP///wD///8A////AP///wD///8A////AAUFBRkAAAAjAAAAIwAAACMAAAAjAAAAIwAAACMAAAAjAAAAIwAAACMAAAAjAAAAIwAAACMAAAAjAAAAIwAAACMAAAAjAAAAIwAAACMAAAAjAAAAIwAAACMCAgIZ////AP///wD///8A////AP///wD///8A////AP///wCgmJTqnJSQ/5iQjP+UjIj/koqG/5CJhf+QiYX/kImF/5CJhf+QiYX/kImF/5CJhf+QiYX/kImF/5CJhf+QiYX/kImF/5CJhf+QiYX/kImF/5CJhf+QiYX/i4SA7QAAABz///8A////AP///wD///8A////AP///wD///8A////AKWcmP////////////////////////////////////////////////////////////////////////////////////////////////////////////////+QiYX/AAAAHP///wD///8A////AP///wD///8A////AP///wD///8AqaCc///////68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7//////5CJhf8AAAAc////AP///wD///8A////AP///wD///8A////AP///wCupaD///////ry7v/68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7/+vLu//ry7v//////kImF/wAAABz///8A////AP///wD///8A////AP///wD///8A////ALKppP//////+vPv//rz7//8tZ///LWf//y1n//8tZ///LWf//y1n//8tZ///LWf//y1n//68+///LWf//y1n//8tZ///LWf//y1n//68+//+vPv//////+QiYX/AAAAHP///wD///8A////AP///wD///8A////AP///wD///8At62o///////68+//+vPv//y1n//68+//+vPv//rz7//68+//+vPv//rz7//68+///LWf//rz7//68+//+vPv//rz7//68+//+vPv//rz7//68+///////5CJhf8AAAAc////AP///wD///8A////AP///wD///8A////AP///wC6sKv///////rz8P/68/D//LWg//rz8P/68/D/+vPw//rz8P/68/D/+vPw//rz8P/8taD/+vPw//y1oP/8taD//LWg//y1oP/8taD/+vPw//rz8P//////kImF/wAAABz///8A////AP///wD///8A////AP///wD///8A////AL2zrv//////+vTw//r08P/8taD/+vTw//r08P/69PD/+vTw//r08P/69PD/+vTw//y1oP/69PD/+vTw//r08P/69PD/+vTw//r08P/69PD/+vTw//////+QiYX/AAAAHP///wD///8A////AP///wD///8A////AP///wD///8AwLWw///////69PH/+vTx//y1oP/69PH/+vTx//r08f/69PH/+vTx//r08f/69PH//LWg//r08f/8taD//LWg//y1oP/8taD//LWg//r08f/69PH//////5CJhf8AAAAc////AP///wD///8A////AP///wD///8A////AP///wDBtrH///////r18v/69fL//Lah//r18v/69fL/+vXy//r18v/69fL/+vXy//r18v/8tqH/+vXy//r18v/69fL/+vXy//r18v/69fL/+vXy//r18v/+/v7/kImF/wAAABz///8A////AP///wD///8A////AP///wD///8A////AMG2sf//////+/Xy//v18v/9tqH/+/Xy//v18v/79fL/+/Xy//v18v/79fL/+/Xy//22of/79fL//bah//22of/9tqH//bah//22of/79fL/+vTy//z8/P+QiYX/AAAAHP///wD///8A////AP///wD///8A////AP///wD///8Awbax///////79fP/+/Xz//22of/79fP/+/Xz//v18//79fP/+/Xz//v18//79fP//bah//v18//79fP/+/Xz//v18//79fP/+/Xz//r18v/48/H/+fn5/5CJhf8AAAAc////AP///wD///8A////AP///wD///8A////AP///wDBtrH///////v29P/79vT//bai//22ov/9tqL//bai//22ov/9tqL//bai//22ov/9tqL/+/b0//22ov/9tqL//bai//22ov/8tqH/+PPy//bx8P/39/f/kImF/wAAABz///8A////AP///wD///8A////AP///wD///8A////AMG2sf//////+/b0//v29P/79vT/+/b0//v29P/79vT/+/b0//v29P/79vT/+/b0//v29P/79vT/+/b0//v29P/79vT/+vb0//j08v/28vD/8+/u//Pz8/+QiYX/AAAAHP///wD///8A////AP///wD///8A////AP///wD///8Awbax///////79/X/+/f1//23ov/9t6L//bei//23ov/9t6L//bei//23ov/9t6L//bei//23ov/9t6L//bei//y2ov/7taH/+rSg//Pw7v/w7ev/8PDw/5CJhf8AAAAc////AP///wD///8A////AP///wD///8A////AP///wDBtrH///////v39v/79/b/+/f2//v39v/79/b/+/f2//v39v/79/b/+/f2//v39v/79/b/+/f2//v39v/69/X/+PX0//bz8f/z8O//8O3s/+zq6P/r6+v/kImF/wAAABz///8A////AP///wD///8A////AP///wD///8A////AMG2sf//////+/j2//v49v/9t6P//bej//23o//9t6P//bej//23o//9t6P//bej//23o//9t6P//Lej//u2ov/6taH/+bOf//eynv/s6un/6efl/+fn5/+QiYX/AAAAHP///wD///8A////AP///wD///8A////AP///wD///8Awbax///////7+Pf/+/j3//v49//7+Pf/+/j3//v49//7+Pf/+/j3//v49//7+Pf/+/j3//r49v/49vT/9vTy//Px8P/w7u3/7Orp/+jn5v/l4+L/4+Pj/5CJhf8AAAAc////AP///wD///8A////AP///wD///8A////AP///wDBtrH///////v5+P/7+fj//bik//24pP/9uKT//bik//24pP/9uKT//bik//24pP/8t6P/+Pb1//b08//z8fH/8O7u/+zr6v/p5+f/5ePj/+Hg3//f39//koqG/wAAABz///8A////AP///wD///8A////AP///wD///8A////AMG2sf//////+/n4//v5+P/7+fj/+/n4//v5+P/7+fj/+/n4//v5+P/7+fj/+vj3//n39v/29PP/9PLx/+/t7P/q6Of/5eTj/+Hg3//d3Nv/2tjY/9jY2P+UjIj/GxoZEv///wD///8A////AP///wD///8A////AP///wD///8Awbax///////8+vn//Pr5//24pP/9uKT//bik//24pP/9uKT//bik//24pP/8t6P/+7ai//Ty8f/x7+7/zsjF/8bBvv+/urj/t7Ox/7Ctq/+qp6X/oZ6b/5SMiO////8A////AP///wD///8A////AP///wD///8A////AP///wDBtrH///////z6+f/8+vn//Pr5//z6+f/8+vn//Pr5//z6+f/7+fn/+ff3//f19P/08vL/8e/v/+3r6//Oycb/+fn4//n5+f/19PT/5OPj/83Ly/+knJjznZeUPP///wD///8A////AP///wD///8A////AP///wD///8A////AMG2sf///////Pr6//z6+v/9uKX//bil//24pf/9uKX//bik//y3o//7tqL/+bWh//izn//t7Oz/6ejo/8/Kx//7+/v/9/f3/+bm5v/Qz8//r6ik862mozz///8A////AP///wD///8A////AP///wD///8A////AP///wD///8Awbax///////8+/r//Pv6//z7+v/8+/r//Pv6//v6+v/5+Pf/9/b1//Tz8//x8PD/7ezs/+no6P/l5eT/z8rH//f39//m5ub/0c/Q/7evq/O5sq88////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wDBtrH///////z7+//8+/v//Pv7//z7+//7+vr/+fj4//f29v/08/P/8fDw/+3s7P/p6en/5eXl/+Hh4f/NyMb/5uXm/9HQ0f++tbLzv7i1PP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AMG2sf///////Pv7//z7+//8+/v/+/v6//n5+P/39/b/9PTz//Hx8P/t7e3/6enp/+bl5f/h4eH/3d3d/8zGw//S0ND/wrq288S9uTz///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8Awbax//////////////////7+/v/8/Pz/+vr6//f39//z8/P/8PDw/+zs7P/o6Oj/5OTk/9/f3//b29v/ycK//8K5tPPEvLg8////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wDBtrHqwbax/8G2sf/BtrH/wbax/8G2sf/BtrH/wbax/8G2sf/BtrH/wbax/8G2sf/BtrH/wbax/8G2sf/BtrHvxLu3PP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  DASH: {
    type: "Dashboard",
    id: 178,
    icon: "data:image/png;base64,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"
  },
  GDT: {
    type: "Graph",
    id: 115,
    icon: "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAABGdBTUEAALGPC/xhBQAAACBjSFJNAAB6JgAAgIQAAPoAAACA6AAAdTAAAOpgAAA6mAAAF3CculE8AAAABmJLR0QA/wD/AP+gvaeTAAAEdUlEQVRYw72XXW8UVRjHf885Z3YXippQUSqIbcAYQqLRkOiFeiEx3nhjSAx3ookfwRs+gDde+xFMvDCIxhgTbogE0WACKlgoIFu67bZbtqXL7Mvs7ux4ceZtZ6ZAauokmz0zffb8f8//ec6cUwmCgO249NNfvgeceETYd2Zb1O11Ys+zT548cGiq8I9L86vUa2t7thOAA4emmH77GEcP2vvI6+uLUDr/C/XaGtsKAPDKNHz6bupBAKd/g5vn7e22A3gDaHWS7AG6/WS87QDdPqy7cfIAtL3/EaDTh3uuVY8A3F4K4JlT+k3gw0fM82Pjc/+nLQF4sLqR3A98mK2BpBz4ZPeuyY/379lfOMHy2jKNjZUZYOsALTu+WYevLwjdPrwqCYDMTM3w8msvceSpozFZAPzjznLlz6s0NlZkC9oAtHvWgdlF+P6SnWZnGcRPAAA4uOswH+z7KCUvnF0+zRWublXbAnhwY0n44XcQAa3AaJBhBsDzPVrD+0BSn96o+5/Ewa6Cn2ftpEalAFIlCMU63O834+wBOkN3bLIvRN4HTj5C89vPguCrKJHVFmy0Q3Ftv50igK7fptlfISm20PYfpPwA4PjufXuPv/DiNKmwOGbxTo1GdaECWACxS87oBEArcAyoLEBn6NL0VgAJ6YT28AHZ7pua3s+xt47A6+8kcAJcu8y5sxdpVBfG4qOMY3EdOkAGwDrQCOeTGIAcgsBz0/DGsfFn3S7w63ikhNlnPiWTKYEIdPwO97wVBCEgoOrOcac9xwR7c/p02rC6PK7kPkhmTYUaA87ICjspgEwJhJ7fYa3fYDDq88f6JVqDdcq6woRk9/NQrH7XjiPR1v2cWyJQ0jAyeYBcE3p+j6bXYK51ld6oixaNFh2WI3O5LVjKACxU8w6IbbhRkAA4RQ4Igjfqcc+dwxt5obBCi8kDhHbL0oIdrzfh8kXo9aD8fK4EJQ1BAUD+PeB36PguWjRKFCoEKGzCjgvLi1b81t/2WXlHYQkcY98sjrZjo6HsJKGxA34wDDO24koUmk0c6HShdxfqNRADSoMugah8D4QpOmbcgWG2CZVoNBoRnQCIQaSgB7y+7QNlQCkQDTqVVqoETmh31IARgJ9dhhqDFgclyrogD+kB3wfCF7vS9mNKyawZByKA9Crwsg5oMWgxcf1F9OY9oBzQQyssOinBJgBKxpdhbi8QBBUDJCUw4hQ7oB0wfiKuNBgHBuqxAApXgRGDCUuQdiDXAyJWbDjKOyDj/2UJmzhgMnuBIGhx0DIMAexSNMoQFJVAO2BG4w7oEsjgoQ6YzUoQ9UDkgIQQWhz8whKUQAeJuIRNGB1zCpow2pIjiFwPVHQlFFZxH5RUmTZ+3oHKTtuIcQkUlMpANxtJpRRuRqkDSSlbgrurVXaUDwMVRiKMQqgBQ27Xb41Nunz7DucmJpIU4zOBS+36jbHYW3MNdj1xAZHk3CLhz679VY8BztTWFiZra+MHicz1Tfh9pjk/P9mcn3+s2Gp1fbJaXX9o7L92vmrt3dmRXgAAACV0RVh0ZGF0ZTpjcmVhdGUAMjAxOC0xMS0wNlQwOToyNjozOSswMDowMOveKmsAAAAldEVYdGRhdGU6bW9kaWZ5ADIwMTgtMTEtMDZUMDk6MjY6MzkrMDA6MDCag5LXAAAAAElFTkSuQmCC"
  },
  GM: {
    type: "Ground Model TIN",
    id: 73,
    icon: "data:image/png;base64,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l/2n15f9qdea/K/Npf2SmZD+WmBY/nB3bv9bXFvSWVlaDAAAAAD///8AmZiaP4yLjf9zc3T/anJo/3mQcv98lnP/eZVw/3eVbv92lG3/dpRt/3aUbf92lG3/dpRt/3aUbf92lG3/dpRt/3aUbf92lG3/dpRt/3aUbf92lG39d5Rt/XeUbf13lG39eZRw/YSRgP52d3X+dXV0/1hYWNJeXV4MAAAAAP///wCop6k/rKyt/52cnv+Pj5D/iIqH/4eJhv+HiYb/h4mG/4eJhv+HiYb/h4mG/4eJhv+HiYb/h4mG/4eJhv+HiYb/h4mG/4eJhv+HiYb/h4mG/4eJhv6HiYb/h4mG/4eJhv6Hiob/kpOS/52dnf+enZ7/c3J0ymdmZwwAAAAA////ALKyswa0s7Q/rKusP6Oioz+cm5w/mJeZP5mYmT+ZmJk/mJeYP5mYmT+ZmJk/mJeYP5mYmT+ZmJk/mJeYP5mYmT+ZmJk/mJeYP5mYmT+ZmJk/mJeYP5mYmT+ZmJk/mJeYP5uamz+hoaI/qKeoP6SkpT+Uk5QreHh5AgAAAAD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  LAB: {
    type: "Label list",
    id: 72,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AAAAAAcAAAAQAAAAEQAAABEAAAARAAAAEQAAABEAAAARAAAAEQAAABEAAAARAAAAEQAAABEAAAARAAAAEQAAABEAAAARAAAAEQAAABEAAAARAAAAEQAAABEAAAARAAAAEQAAABAAAAAD////AP///wD///8A////AP///wB1cXELIB8fKBAQEDYQEBA2EBAQNhAQEDYQEBA2EA8PNhAPDzYQDw82EA8PNhAPDzYQDw82EA8PNhAPDzYPDw82Dw8PNg8PDzYPDw82Dw8PNg8PDzYPDw82Dw8PNg8PDzYKCgovAAAAJgAAAA7///8A////AP///wD///8A////AJWRkfGcmJj/nJiY/5uXl/+bl5f/mpaW/5qWlf+ZlZX/mJSU/5iUlP+Xk5P/l5OT/5aSkv+WkpL/lZGR/5WRkf+UkJD/lJCQ/5SQkP+Tj4//k4+P/5OPj/+Sj4//ko+P/4WCgvMAAAAmAAAADv///wD///8A////AP///wD///8AlpKS//39/f/9/f3//f39//39/f/9/f3//f39//39/f/9/f3//f39//39/f/9/f3//f39//39/f/9/f3//f39//39/f/9/f3//f39//39/f/9/f3//f39//39/f/9/f3/ioaG/wAAACYAAAAO////AP///wD///8A////AP///wCXkpL//f39//n08v/37uv/9+3q//bs6f/26+j/9uvn//Xq5v/16eX/9Ojk//Tn4//05+L/8+bh//Pl4P/z5eD/8+Xg//Pl4P/z5eD/8+Xg//Pl4P/z5eD/9u7q//39/f+Khob/AAAAJgAAAA7///8A////AP///wD///8A////AJeTk//9/f3/+PLv//Xo5P/05+L/9OXg//Pk3//y4t3/8uHb//Hg2f/w3tj/8N3W/+/c1f/v29P/7tnS/+7Z0f/u2ND/7tjQ/+7Y0P/u2ND/7tjQ/+7Y0P/06OP//f39/4qGhv8AAAAmAAAADv///wD///8A////AP///wD///8AmJST//39/f/58/H/9uvm//Xp5f/16OP/9Obh//Pl4P/z497/8uLc//Hh2v/x39n/8N7X//Dc1v/v29T/79rT/+7Z0v/u2NH/7tjQ/+7Y0P/u2ND/7tjQ//To4//9/f3/i4aG/wAAACYAAAAO////AP///wD///8A////AP///wCZlJT//f39//n08v/37en/9uvn//bq5v/16eT/9Ofj//Tm4f/z5N//8+Pd//Lh3P/x4Nr/8d/Y//Dd1//w3NX/79vU/+/a0v/u2dH/7tjQ/+7Y0P/u2ND/9Ojj//39/f+Lh4f/AAAAJgAAAA7///8A////AP///wD///8A////AJmVlf/9/f3/+vXz//fu6//37er/9erm/+rg3P/j2dT/6NvX//Hk3//05eD/8+Te//Li3f/y4dv/8eDZ//De2P/s2tP/4c/I/93Kw//jz8j/7NfP/+7Y0P/06OP//f39/4uHh/8AAAAmAAAADv///wD///8A////AP///wD///8AmpaV//39/f/69vT/+PDt//jv7P/p4d7/a5m0/0Ke0P9WmLz/2s/M//Tn4v/05uH/8+Xg//Pj3v/y4tz/797Y/9HCvP9Nlbz/QZrL/3KSpf/k0Mn/7tnS//To5P/9/f3/jIeH/wAAACYAAAAO////AP///wD///8A////AP///wCblpb//f39//r29P/58e7/+PDt/+fg3P9Knsz/htT+/3nQ/v+WnaL/7+Tg//Xp5P/05+L/9Obh//Pk3//p29X/hZKb/4DS/v+G1P7/WZKx/+TRyv/v29T/9enl//39/f+MiIj/AAAAJgAAAA7///8A////AP///wD///8A////AJuXl//9/f3/+vb0//nx7v/58e7/8urm/5miqf9sy/7/dc7+/0qcyf/g19P/8+jk//Ln4v/y5eH/8eTf/9rNyP88oNb/dc7+/2PI/v+noqH/69rU//Dd1v/16ub//f39/4yIiP8AAAAmAAAADv///wD///8A////AP///wD///8AnJiX//39/f/69vT/+fHu//nx7v/48O3/1s/M/zK1/P9hx/7/Qrz9/5ecoP+qq63/qqus/6qpq/+pqar/kZaa/0u//f9hx/7/Lqzw/9bHwv/x4Nr/8d/Z//br6P/9/f3/jYmJ/wAAACYAAAAO////AP///wD///8A////AP///wCdmJj//f39//r29P/58e7/+fHu//nx7v/r5OH/aJy5/0i+/v9Ivv7/Rb3+/0W9/v9Fvf7/Rb3+/0W9/v9Fvf7/SL7+/0i+/v96mKr/6drV//Lj3f/y4dv/9u3p//39/f+NiYn/AAAAJgAAAA7///8A////AP///wD///8A////AJ2Zmf/9/f3/+vb0//nx7v/58e7/+fHu//bu6/+7ubr/Obj+/y21/v8ttf7/L7b+/y+2/v8vtv7/L7b+/y21/v8ttf7/NLf9/8W8uf/y5eD/9OXg//Pk3v/37uv//f39/46Kiv8AAAAmAAAADv///wD///8A////AP///wD///8AnpmZ//39/f/69vT/+fHu//nx7v/58e7/+fHu/+HZ1/89puD/IbH+/zS3/v9xma7/k6Ww/5Klr/9lmbb/K7T+/yGx/v9Noc3/49jU//Xp5f/16OP/9Obh//fv7P/9/f3/j4qK/wAAACYAAAAO////AP///wD///8A////AP///wCfmpr//f39//r29P/58e7/+fHu//nx7v/58e7/8enn/42mtP8vtv7/KrT+/2egwP/m39z/49vZ/1aizP8qtP7/Nrj+/5+qsf/x5+T/9uvn//bq5v/16eT/+PHu//39/f+Pi4v/AAAAJgAAAA7///8A////AP///wD///8A////AJ+amv/9/f3/+vb0//nx7v/58e7/+fHu//nx7v/48O3/0cvI/0O7/f9BvP7/Pbn8/9XOy//OyMX/R739/0G8/v85uPv/18/N//bt6v/37er/9uzo//br5//48u///f39/5CLi/8AAAAmAAAADv///wD///8A////AP///wD///8AoJub//39/f/69vT/+fHu//nx7v/58e7/+fHu//nx7v/p4t//XqXM/1fE/v9exv7/l6Wt/4ahsP9bxf7/V8T+/3Civv/s5OH/+PDt//jv7P/37ur/9+3p//nz8f/9/f3/kIyM/wAAACYAAAAO////AP///wD///8A////AP///wCgnJv//f39//r29P/58e7/+fHu//nx7v/58e7/+fHu//Xt6v+xs7X/Ysf+/2bJ/v9FodP/N6zr/2bJ/v9bxP3/v7y8//bu6//58e7/+PDt//jw7P/47+v/+vTy//39/f+RjYz/AAAAJgAAAA7///8A////AP///wD///8A////AKGcnP/9/f3/+vb0//nx7v/58e7/+fHu//nx7v/58e7/+fHu/97X1P8zsfX/c83+/1PC/f9ix/7/c83+/0Ko3v/j29n/+fHu//nx7v/58e7/+fDt//jw7f/69fP//f39/5KNjf8AAAAmAAAADv///wD///8A////AP///wD///8AoZ2c//39/f/69vT/+fHu//nx7v/58e7/+fHu//nx7v/58e7/7+jl/4Gbqf980f7/gNL+/4DS/v92z/7/k6Gp//Lq5//58e7/+fHu//nx7v/58e7/+fHu//r29P/9/f3/ko6O/wAAACYAAAAO////AP///wD///8A////AP///wCinZ3//f39//r29P/58e7/+fHu//nx7v/58e7/+fHu//nx7v/37+z/y8XD/0i9/f+J1f7/idX+/zi3/P/Uzcv/+PDt//jw7f/37+z/9e3q//Xt6v/17er/9vLw//r6+v+SjY3/AAAAJgAAAA7///8A////AP///wD///8A////AKKenf/9/f3/+vb0//nx7v/58e7/+fHu//nx7v/58e7/+fHu//nx7v/o4d7/Z5iy/zu5/f87uf3/d5mr/+zl4v/48O3/9u7r/+/n5P/o4N7/5d7b/+Xe2//n4+L/7+/v/5CMi/8AAAAnAAAADv///wD///8A////AP///wD///8Ao56e//39/f/69vT/+fHu//nx7v/58e7/+fHu//nx7v/58e7/+fHu//fv7P/n4N3/2NHO/9jRzv/p4t//9+/s//jw7f/z6+j/49vZ/9LLyP/MxcP/zcbE/9TQz//h4eH/j4uL/wAAACUAAAAI////AP///wD///8A////AP///wCjnp7//f39//r29P/58e7/+fHu//nx7v/58e7/+fHu//nx7v/58e7/+fHu//nx7v/58e7/+fHu//nx7v/58e7/+PDt//Lq5/+fm5r/m5aW/5qWlv+ZlZX/mJSU/5aSkf+RjY33IB8fDf///wD///8A////AP///wD///8A////AKSfn//9/f3/+vb0//nx7v/58e7/+fHu//nx7v/58e7/+fHu//nx7v/58e7/+fHu//nx7v/58e7/+fHu//nx7v/48O3/8urn/5uXlv/n5uj/5+bo/97d3v/HxMX/lpKS+HVyck7///8A////AP///wD///8A////AP///wD///8ApJ+f//39/f/69vT/+fHu//nx7v/58e7/+fHu//nx7v/58e7/+fHu//nx7v/58e7/+fHu//nx7v/58e7/+fHu//jw7f/y6uf/nJeX/+Tj5P/e3d7/x8XF/5eTk/h5dXVP////AP///wD///8A////AP///wD///8A////AP///wCkoJ///f39//r29P/58e7/+fHu//nx7v/58e7/+fHu//nx7v/58e7/+fHu//nx7v/58e7/+fHu//nx7v/58e7/+PDt//Pr6P+cmJf/29na/8fFxf+YlJT5enZ2T////wD///8A////AP///wD///8A////AP///wD///8A////AKWgoP/9/f3/+/j3//r29P/69vT/+vb0//r29P/69vT/+vb0//r29P/69vT/+vb0//r29P/69vT/+vb0//r29P/69vT/9/Px/52Zmf/EwsP/mZSV+Hp3d0////8A////AP///wD///8A////AP///wD///8A////AP///wD///8ApaCg//39/f/9/f3//f39//39/f/9/f3//f39//39/f/9/f3//f39//39/f/9/f3//f39//39/f/9/f3//f39//39/f/8/Pz/npqZ/5yXl/iEgYBO////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wCloKDspaCg/6WgoP+koJ//pJ+f/6Sfn/+jnp7/o56e/6Kenf+inZ3/oZ2c/6GcnP+gnJv/oJub/5+amv+fmpr/npmZ/52Zmf+blpbzmJSUS////wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  LIFEE: {
    type: "Lifetime Estimator",
    id: 193,
    icon: "data:image/png;base64,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"
  },
  LL: {
    type: "Layer List",
    id: 98,
    icon: "data:image/png;base64,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"
  },
  MASG: {
    type: "Master Group",
    id: 177,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wASAAADEwAACRYAAA0XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFgAADRMAAAgSAAAC////AP///wD///8AEQAAARMAAA8VAAApMhcQQlAvIVRQLyFUUC8hVFAvIVRQMCFUUTAhVFEwIVRRMCJUUTAiVFEwIlRRMCJUUTAiVFEwIlRRMCJUUTAiVFEwIVRRMCFUUDAhVFAvIVRQLyFUUC8hVE8uIVMpEAw+FAAAJhMAAA0RAAAB////AP///wAUAAADSCkdKJxtTb2yfln8s39a/7N/Wv+1gVr/uINc/7mEXv+8hl7/vIZe/7yGXv+9h17/vYde/72HXv+9h17/vYde/72HXv+8hl7/vIZe/7yGXP+5hF7/uINb/7WBWv+zf1r/s39a/7F9WfmXaUqsMBcQHBQAAAL///8A////ABQAAAOseVa2s39a/7N/Wv+1glv/vIZe/8KJX//GjWP/yJBk/8uQZP/MkWT/zJFm/82SZv/Nkmb/zZJm/82SZv/Nkmb/zZJm/8yRZv/MkWT/y5Bk/8iQZP/GjGP/wYlf/7yGXP+1glv/s39a/7N/Wv+qd1WXFAAAAv///wD///8ArntXIbN/Wv6zf1r/uINc/8GJX//IjmT/zpNo/9OWaf/WmGv/15hr/9iba//Ym2v/2Jtr/9iba//Ym2v/0JVq/6p6b/+gc2//oHNv/6Bzb/+fcG//nnBv/6Z2bf/MkGb/x45j/7+IX/+4g1v/s39a/7N/Wvazf1oI////AP///wCzf1o+s39a/7WCW//BiV//y5Bk/9OWaf/Ym2v/3Z1u/+Ggb//konD/5KJy/+Sicv/konL/5KJy/+Sicv+/iG7/TkCa/1pWw/9kXsX/aGDF/2Jdxf9bWMT/QjaV/82Rav/Slmn/yZBk/7+IX/+1glv/s39a/7N/Wh7///8A////ALN/Wj+zf1r/vYde/8iQZP/Tlmn/25tt/+Khb//npXL/6qZ0/+Ojc//foHH/4KBx/+Cgcf/goHH/4KBx/7uHcf9eVbD/hoX4/5mQ/P+flPz/lY78/4iJ+f9MQ6b/1phu/9qbbf/Slmn/x45j/7yGXP+zf1r/s39aH////wD///8As39aP7WCW//Di2H/zpNo/9iba//ioW//6qZ0/+6qd//zrHj/oXpc/4xzYf+VeGL/lXhi/5V4Yv+VeGL/fmdq/1lXtP+Chvn/ion9/4yI//+Dg/3/e4D8/0tDqP/bnXP/4aBv/9eYa//Okmb/wYlf/7WBWv+zf1of////AP///wCzf1o/uINc/8eOY//Tl2r/3Z9u/+aldP/uqnf/9K55//ixev+Vc1v/vpZ4/92jd//donX/3aJ1/92idf+7inn/Yluz/5Sc+f+boP3/mZz9/5CV/f+HkPr/TUao/+Khdv/mpHL/3J1u/9OWaf/GjGP/uINb/7N/Wh////8A////ALSBWj+8hlz/y5Bk/9eYav/ioW//6qd1//OueP/4sXz//bR9/5l3Xf/Sn3n//rV///61f//+tX///rV//9KWef9aUav/iZLo/5KZ7P+RmOz/jZXs/4SO6v9KQ6P/5KN3/+qmdP/hoG//1phr/8iQZP+5hF7/tIFaH////wD///8AtYFaP72HXv/Nkmb/2ptr/+Sicv/uqnf/9K55//qzff/+tX//l3Ze/9Sie///uIH//7iB//+4gf//uIH/5aV9/4Vjiv92XJT/d12U/3ddlf93XJT/dluT/39ciP/tqXj/7Kl3/+ShcP/XmGv/y5Bk/7yGXP+2glof////AP///wC1gls/vohf/8+Wav/epXv/6K+D//C2iv/3u47//L+S///BlP+mjHf/3LGO///BkP//vov//7qE//+5gv/8t4H/7K99/+esfP/nrHz/56x8/+ere//mqHn/6Kp5//Suev/uqnf/5KJy/9iba//MkWT/vIZe/7WCWx////8A////ALWCWz++iF//0Zlu/+GrhP/ptIr/8bqQ//i/lP/8w5j//8Wb/66Xhf/iu53//8ui///MpP//zaX//8qg/+W7iv99n1T/ap5O/2yfT/9sn1D/a55P/2mcTP96mEr/7qx3/+6qd//konL/2Jtr/8yRZv+8hl7/uINbH////wD///8AtYJbP76IX//RmnD/4a2H/+q1jf/xu5P/+MGX//zFm///x57/r5iH/+S+oP//zaX//86n///Pqf//0Kr/3sSc/47Hjv+Z6aj/jeqd/4HolP955o3/bt2D/0mcRP/pqnX/7qp3/+Sicv/Ym2v/zZJm/72HXv+4g1sf////AP///wC1gls/vohf/9Kbcv/ir4v/67iQ//K9lv/4wpr//Mae///Jof+rl4f/0rSc/+a+n//lv6D/5sCi/+bBpP/NvZv/lM6X/6v3u/+y+8H/rfy8/4n5n/9y7oz/TKFI/+mqdf/uqnf/5KJy/9iba//Nkmb/vYde/7iDWx////8A////ALWCWz++iF//0p10/+Oxjv/ruZP/8r+Z//jEnf/8yKH//8qk/6iXiv+2ppr/v6uc/7+snf/BrZ//wa+g/7Kwmf+Yz5//tffD/7f6xf+3+sT/s/nB/5fxqv9OoUv/6ap1/+6qd//konL/2Jtr/82SZv+9h17/uINbH////wD///8AtYJbP76IX//Tnnb/5LSR/+y8lv/zwZz/+cag//zKpP//zKf/sZ+R/+XDqf/3zKv/982s//fOrv/30LD/3cmn/6LRo//G99H/y/nV/8r61P/I+dP/wvXN/5XGkv/qr33/7qp3/+Sicv/Ym2v/zZJm/72HXv+4g1sf////AP///wC1gls/vohf/9Sgef/ltpT/7L6a//PDoP/5yKP//Mun///Oqv+zopX/68er///Tsf//1LP//9W0///Wtf/mzav/oMmZ/6rXrP+u2rD/r9ux/7Dcsv+w27L/rMyj//TStf/vsYL/5KJy/9iba//Nkmb/vYde/7iDWx////8A////ALWCWz++iF//1aJ8/+W4l//twJ3/88Wi//nJpv/8zar//8+t/7anmv/tyq///9W0///Wtf//17f//9e4//jWt//hz67/3M6t/93Qr//e0bL/39Kz/9/StP/l1bj/+drC//bTuf/lpnn/2Jtr/82SZv+9h17/uINbH////wD///8AtYJbP76IX//VpH3/5rqb/+7CoP/0x6X/8ceo/+7Iqv/yy63/sayj/+TLtf/y0bX/8tK2//vWuP//2bv//9q9///bvv//3MD//9zB///dw///3sT//93E//3dxf/73MX/+NvF//DKr//Ym2z/zJFm/7yGXv+4g1sf////AP///wC1gls/vohf/9amgP/mvZ7/7sSj//TJqf+3wLj/oMjO/6bJzv+dxs//qs3S/6rO0v+szdH/2tDA///avv//27///9zB///dw///3sT//9/F///fxv//38f//d/H//veyP/43cj/9NrH/+Gzj//MkWT/vIZe/7WCWx////8A////ALWBWj+9h17/16iF/+e/oP/uxaf/9cus/6bCxP+n5vj/s+n5/73s+f+86/n/tOr5/6ri8f/P0Mb//9zA///cwv//3cP//97F///fxv//4Mj//+DJ///gyf/938r/+9/J//jeyv/13Mn/7tO//8ySZv+8hl7/toJaH////wD///8AtIFaP7yGXv/WqIb/5sCk/+3GqP/zy63/qsXH/67r/f+37f3/wO/8/77v/f+37f3/ruX0/9LSyf//3ML//9zD///dxf//3sb//9/H///gyf//4cr//uHK//zhy//638z/997L//Tdy//w2sr/1aqI/7mEXv+1gVof////AP///wCzf1o/uINc/9Wpiv/mwaf/7Mer//HMsP+tx8j/uu78/8Pw/f/G8f3/w/D9/77v/f+05/X/09TL//3cxP/93cX//d7G//3fyP/938n//eDK//3hzP/84c3/++HN//ngzf/2383/893M//DbzP/du6L/uINc/7SBWh////8A////ALN/Wj+1glv/1KqM/+TBqf/qx63/78yx/6/Iyv/G8Pv/0fL7/9Pz/P/S8/z/z/L8/8Hp9P/T1Mv/+9zF//vdxv/73sj/+9/J//vfyv/74Mv/++HN//vhzf/54c7/+ODO//Xfzv/y3s7/79zO/9y7o/+1gVr/s39aH////wD///8As39aP7SBWv/Rq47/4sKr/+fHr//ty7P/t8fE/6rV3/+t1t//sNjg/7LZ4f+z2uL/tdjf/9jUyv/428b/+NzI//jdyf/43sr/+d/M//ngzf/54M7/+ODO//bg0P/1387/897P//Hdz//u3M7/276p/7N/Wv+zf1of////AP///wCzf1o/s39a/82ojP/fwav/5cav/+nLtP/iy7j/3cy8/9/Ovv/h0cH/4tLC/+PTxP/k1cb/7tfF//Xbx//13Mj/9dzJ//Xdyv/23sz/9t/N//bfzv/1387/9N/P//Lez//x3s//793P/+zbzv/WuqT/s39a/7N/Wh////8A////ALN/Wiezf1r/wJR1/9vArf/hxbD/5cm0/+nNuf/s0Lv/7dG9/+/Tv//v1cH/8NXC//DXxP/x2Mb/8dnH//Layf/y28r/8tvL//LczP/y3c3/897O//Ldz//x3tD/8N7Q/+7d0P/s28//6trO/8Wdgf+zf1r6s39aDP///wD///8A////ALN/WsGzf1r/wZZ4/9Kwl//Yt5//3Luj/969pf/hv6b/48Gp/+TCqf/kxKv/5MSs/+XFrf/lxq7/5cev/+bIsP/myLH/5smy/+fJs//mybP/5sm0/+TItP/ix7P/38ay/9m/q//Gn4P/s39a/7N/WqL///8A////AP///wD///8As39aGbN/WsGzf1r/s39a/7SBWv+1glv/uINc/7yGXv+9h17/vohf/76IX/++iF//vohf/76IX/++iF//vohf/76IX/++iF//vohf/72HXv+8hlz/uINc/7WCW/+zf1r/s39a/7N/Wv6zf1qus39aDf///wD///8A////AP///wD///8A////ALN/Wiezf1o/s39aP7N/Wj+zf1o/tYFaP7aCWj+1gls/uINbP7iDWz+4g1s/uINbP7iDWz+4g1s/uINbP7iDWz+1gls/toJaP7WBWj+zf1o/s39aP7N/Wj+zf1o+s39aIP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  NGX: {
    type: "GeoExplorer",
    id: 155,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wADAwMBAwIBBQIBAAT///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wAWFhcCJCQkFyMjJDQXFhVVCwsJTQcGBCAEBAIE////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AKSosA0VGRzZKSkybSUpK7TY2Nf8aGRf4CwoIrAkJBy3///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wA6Ozw8UFFRy2tqav9wbGr/aV5X/1pJQP8xJiDzExMSihEREBX///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AExMTFS4vL8JOTk3/cmpl/qCDdP+7jnb/vYVo/nNSQf8mJibZGhoZWAkIBwb///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wAKCQhkHR0c/jcxLf+FW0X/t3dW/7p3Vf+pakn/clJD/z4+P/4hIB+oCgkHJv///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AAcGBLIPDQv/SSwf/6VdO/+tZD//rGRC/5JeRv9rXVf/UVFS/ycnJugMDApiBgUECP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8ABwYEvg4KB/9yPy3/q19G/qZeRP+WXkr/hnBo/nRzcv9WVlb/MjIy/hkZGLEODQwp////AP///wD///8A////AP///wD///8A////AP///wD///8A////ACIiIgoiIiEsGhoaNxAPDxf///8A////AP///wD///8A////AP///wAHBgRrCwgG+0kpHf94RTX/ck1B/2xbVv90cnH/dXV2/1tcXP9GRkb/Li8u8BoaGWUODg0K////AP///wD///8A////AP///wD///8A////ACAhIgYzNDU7Ojs9nDIyM8UmJibLGhoZnQ0MCzL///8A////AP///wD///8A////AAcGBBMJCAaJGBIP+ywgHP81MC3/RkZF/1hZWf9oaGn/ampr/11dXv9GRkb/KCgnwhQTEi0EBAMB////AP///wD///8A////AP///wAPDw8GKiorTEFBRM5LTE72RkND/kk8N/8xJyH0EA8MkgcGBR3///8A////AP///wD///8A////AAgHBRgKCQeCDAwK8xUVE/8mJyX/PT4+/l1dXf91dXX/cHBw/lpaWv82Njb3EhEQfwYGBBD///8A////AP///wD///8AAgICAQwMCiwkJCXWT09R/WZbV/+WbVr/pGhK/3JHMP8kGRPqCAcFZgUFAwr///8A////AP///wD///8A////AAcGBBQIBwVeCQgG2xAPDv8nJyb/SEhI/2hoaP95eXn/bGxs/zk5OP8PDg3fBwYEMgMCAgH///8A////AP///wAFBAMICwoIlicnJ/1WSEL/m2RH/69qRf+uZD//fU87/ywkIf4LCgjHBwYENP///wD///8A////AP///wD///8A////AAgHBRUIBwWLCAcF/xMSEf8uLi3/T09O/25ubv9ra2r/Jycl/wkIBv0IBwWUBgUDD////wD///8A////AAcGBA4LCwnoMSsn/3JCLf6qXzv/ql49/p5aQf9mSD//Kysr/hIREPwJCAZ9BgUEEf///wD///8A////AP///wAJCQkBEhEQMAgHBeQIBwX/CQgG/hcXFf80NDP/QEBA/iUlJP8NDQz/CAcF/ggHBfMHBgQ3BgYFAf///wD///8ABwYEEQkIB/ouIR3/m1Q9/6ZaQf+fWkX/f1pO/09LSf8uLi7/Gxsb/wwLCuQSEhFKHx8fMxwbG0YWFhYeCwsJARISEgcsLS1iGBgX/Q8ODf8KCgj/CQgG/woJB/8PDw3/GBgX/w4NDP8IBwX/CAcF/wwLCaIdHBsJ////AP///wAGBQMKCAcFtCAWEfp6RTP/hlBA/3RbU/9ta2r/UVJS/zc4OP8jJCT/FBMS/x0dHf40NDX/NDQ2/yAgIeEPDg0uHBwbBkhISTpFRUXnKCgn/x8fHv8ZGRj/IyIi/y0uL/8YGBf/CQgG/wgHBf8IBwX/GhkYzy8vLwz///8A////AAQDAgEIBwUnDQwKuhwcG/Y+Pz//Z2dn/nV1df9jY2T/Q0RF/isrK/8fHx7/ERAQ/hwcHf8eHh7/GBgY/hQTE9E8PDxQSkpMfEhISuc4ODn/MzQ0/j8/QP9RUlT/PT0+/hUVFP8JCAb/CAcF/gkJB/8zMjK1SkpLCv///wD///8A////AAUFAwEKCgglEhIQpigoJ+k/QD/+WFhZ/2lpaf9bW1v/Pz8//yoqKv8aGRn/DQ0M/wsLCf8YGBj/LS4v/09PUf4+PkD/Ly8w/zAwMfkoKSjzOjs7/0dHSP9CQ0T/LS0u/xYWFf8REA//IiIh+F5eX2ZfXmAF////AP///wD///8A////AP///wAJCQcZCwoIeBQUEtI3Nzb5YWFh/29vb/9ZWVn/PT4+/x4eHf8KCQj/ExIR/ycnKP8oKSn/Kyss/zU1Nv86Ojr7RUVF0zg5OLA3NzbuRkZH/1FSU/9OT1D/Ojs7/zY2Nf9NTk/WamprHf///wD///8A////AP///wD///8A////AP///wAGBQQLCwoJSxsbGq49PT3rY2Rj/mhoaP9BQUD/FhYU/hIREP8rKyz/ISEh/i4uLv8pKSn/UlJS/ltbXPhZWVnIVVVVhUBAQKFDREPeWltc+Gxtb/9sbG3/Xl5g/kxMTbZRUVIU////AP///wD///8A////AP///wD///8A////AP///wAGBgQCEBAPKSIiIH02NjbQPj49+iIhH/8fHh3/OTk6/yoqKv8WFhX/LS0s/y0tLf9BQkL/S0tM/zs7O/5JSEnTS0tLdzs7PGlGR0i7W1td+Gpqa/9qamv7bW1ugk5OTwz///8A////AP///wD///8A////AP///wD///8A////AP///wD///8ADw8ODBAPDlEPDw67Hh4e9UZGSP9YWFv/Ly8w/w4NDP8JCAb/ISEh/zo7Pf8uLzD/GBgX/zAxMftNTU7EQkNCRigoKEkbGhqwLSwsz2dnZ6CTk5UrS0tMAv///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8ACAgHBRMTEjopKiujQ0NG8FJSVf9LTE7/MTIy/hEREP8RERD/LC0u/jM0Nf8mJif/Njc4/k1NTvJTU1R8Li4tEhIREDEbGxtFQkNDIFtbXAP///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AExMTASgpKig1NTeIQkJF61JTVf5SUlX/ODk6/yEhIf8qKiv/OTo7/zg4OvREREbCUVJUfF1dXzI3NzcF////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////ADAxMxk5OjxpQUJE4l1dYP5vb3L/T09Q/zk5Of9hYWLqXV1fiUpKTDE8PT8Q////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////ACwtLgw4OTs9U1RWYGBgYW4wMC/XREVG33x8foWCgoQY////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////ABMTEwEdHR4IIiEgCxwcHCU6OzwnYGBhE////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  NWNET: {
    type: "Distribution Network",
    id: 135,
    icon: "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAE4klEQVRYw+2UW4hVZRTHf+vbl3Obi6M2OkJKYGjK5IWgq4TdnuqlIISiwB4CKUKEokIIUrTooZegoMeeegmilx6CKIosDZQo7aLpDOOM4swcz8y57P193+ph7+PsUfNSai9tWGetc87e3/r9/2ux4f/rX1zuJBv9BPf8V83X+AlaOoG1Y2y68QBjfKbjqI4b9SfZ50aRG9d8hM06hteZHart91XHUDfCkzekuT2K+BF+0NPLVP1hVT2uOrlR/Qi/uWNEV3ueuWoCzxaBO+h5CcQCs9CzAxFWiuf56wpgf6ZklN2UboPy3UADmIFoFZTvB2WnPUzvdQMQ2CaGW+h7BjgLTANTWe57FjFmUBwvXxcAd4gFAq9T2wClZUB9fkQD0LsZMWx3hxi65gCivCbGLGLgYdB6rn46B8jzgkcRE9XwvHFNAex3LMfzIrVhoARuGuwUuCnwU+CnszAB9G/CKFvtPlZfMwBJ2SUalKmug04dOlOQTENah6Se1Un+W89dIOXQWPZc0dmXu8F9wQYTs5/BVYaFG8FEIEEWJgDyWs1cntwHo1+rS9gUPsg3lzo/vCyi4y0kNJSGMoUS5s3zLCaDoJsDqK6E8IBIq/k2cO8/dqDzKY9EMZ/L4iXQvzxTfK55mDWXgguYuagfRUd/xCY8Hj/GJ1cN0PgYUypxICqxnp4a9C7I7D8X8fzmXYAulAeOf0s60zpsLcPVJ7BXNwLlKVHW44HmLLRnL4IfQhBDWIZSFUq9OVjuQt9SpHFstXM8B3xwxQ6c+YhSFHCkWmFFEOWu6jmw+bl4kgBxFSq9UKkBBjd+glYjOZmk3LroaS5QcVEHvOcFiVihCjjA5g2LUYSQQu40YaYJYQC1GlKKYSYZUmU7sOuyDpz8kIE44vdKzMJSAEbI5llsWoQ4/zQzv1aFtoNmwlnrWLl0K6eLj1zwIlJ4VWCh+Ey9pkA3EqDzN5EU/s/v1yQ7Q3y2Ed6z85IO/Pkey+OII5WYcsVABIgD6Sr2hXz+HnTVF7JK9l6yAk0PrYQktaxZsY0/LroDXnlTlLK4XL1m9OqzPA+iOIauDFNonteafzeAKLFz7Aa2XODAr++yLgg4UAkJqgZKQKhgfO6CvwIHZA5CDWgA3oATaAMtD02Lt5Y7V21n/zwHnGOPQODJLDOSKTc5hNE5F+R8AMlrmTPGa/a8M3loFt5hUPYCD51z4OBeKUehNgUkFogNhCYXo9kOdPdAtGBbXmthk1Tmhwe8gPWQKCQeFNQ6Bm5/hXoI8M6XN3fuu6W+66ZK84FQXBgZDUPR0EBghEDAiGY8kvfv5sIUNP/wCqqCV8V7cB6x1uOsGptqYCfb5a++P9HXgFFkeHi4Cgz0+MaSJeHkUH/VDi6tdRYP9biewSrhgjJBT4SUQyQOkDAfj5GC9bnlTnOlDm1ZtJGgU23cqSbpWCNqjM/GZ2aa4akxBic6Uh4HpkLAq2rqJOh4lVnnpZE4E3esdy2rcZwSCQROManHhAYxggQyNwqvmdXOo9ajHYdvW3zTYlsW27YmSZw0vErDEjQVaatqKiJeANauXSuROKlIJ1gc1oO+qBNVIxdWQh/HgY9LoUaBaCQioRGMEQ0EjOkunYJXyez2OFCbekk7zqSJlbRlg6RpTTqdlO2k63dtLbmDP/3iAf4CTpBhhqpv5zQAAAAASUVORK5CYII="
  },
  REHABP: {
    type: "Rehabilitation Planner",
    id: 196,
    icon: "data:image/png;base64,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"
  },
  RISK: {
    type: "Risk Analysis Run",
    id: 195,
    icon: "data:image/png;base64,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"
  },
  SEL: {
    type: "Selection List",
    id: 31,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wAAAtVYAALVxwAC1fYAAtX/AALV/wAC1f8AAtX/AALV/wAC1f8AAtX/AALV/wAC1f8AAtX/AALV/wAC1f8AAtX/AALV/wAC1f8AAtX/AALV/wAC1f8AAtX/AALV/wAC1f8AAtX/AALV9QAC1ccAAtVW////AP///wD///8AAALVfwAC1f8AAtX/AALV/QAC1eUAAtXfAALV3wAC1d8AAtXfAALV3wAC1d8AAtXfAALV3wAC1d8AAtXfAALV3wAC1d8AAtXfAALV3wAC1d8AAtXfAALV3wAC1d8AAtXfAALV3wAC1eUAAtX9AALV/wAC1f4AAtV8////AAAC1VgAAtX/AALV9wAC1XMAAtUQ////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AAAC1REAAtV1AALV+AAC1f4AAtVWAALVyAAC1f8AAtVz////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wAAAtV1AALV/wAC1ccAAtX2AALV/QAC1RD///8A////AP///wD///8AAwQCAgwYCiIULxRNEy4URwsVCRsCBAIB////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wAAAAAA////AAAC1REAAtX9AALV9QAC1f8AAtXl////AP///wD///8A////AAoSCBUtYyamN5g5+TqkRv45pEb/NZg59yxiJqILFAkV////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AAAAAAD///8A////AAAC1eUAAtX+AALV/wAC1d////8A////AP///wAFCAMGMm4ruVSpWv5tt37+eLyJ/nC6hf9ltnv/S6dS/zRxK7sGCgQG////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AAAAAAP///wD///8AAALV3wAC1f8AAtX/AALV3////wD///8A////ABgxE01AplD+Q6xf/jmpVf44qlf+Oapa/zqrXP8/rmP/PaVN/ho0FUz///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wAAAAAA////AP///wAAAtXfAALV/wAC1f8AAtXf////AP///wD///8AJlsmjzipVf45qln+Oqxd/jquYP47r2P/O69k/zuwZf47rmL+KFwnif///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AAAAAAD///8A////AAAC1d8AAtX/AALV/wAC1d////8A////AP///wAmZDCZOqxc/zuuYf88sGb/P7Jr/0SzcP9ItHP/SbV0/0e0cv8tZjeS////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AAAAAAP///wD///8AAALV3wAC1f8AAtX/AALV3////wD///8A////ABxJJWo7r2T/P7Jr/0m1dP9UuHz/XbqD/2K7h/9ju4j/YbqG/yVKLWL///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wAAAAAA////AP///wAAAtXfAALV/wAC1f8AAtXf////AP///wD///8ACRQJFDmZXN5Qt3r/YLqF/229j/52v5b/e8Cb/3zAnP9qn37/cnNy6v///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AAAAAAD///8A////AAAC1d8AAtX/AALV/wAC1d////8A////AP///wD///8AFCoYMU6WaNF1vpX+g8Kh/o3Fqf+Sxq3/d56H/5WYlf+cnJz/dnZ26P///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AAAAAAP///wD///8AAALV3wAC1f8AAtX/AALV3////wD///8A////AP///wD///8ABw0ICSE6J0Y/YEt0Q2FOdC04MIKSk5Lwqamp/ra2tv+Wlpb/cXFx6P///wD///8A////AP///wD///8A////AP///wD///8A////AP///wAAAAAA////AP///wAAAtXfAALV/wAC1f8AAtXf////AP///wD///8A////AP///wD///8A////AP///wD///8A////ADQ0NFabm5vvr6+v/qurq/+Ghob/b29v6P///wD///8A////AP///wD///8A////AP///wD///8A////AAAAAAD///8A////AAAC1d8AAtX/AALV/wAC1d////8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////ADMzM1abm5vvpaWl/piYmP9/f3//bW1t6P///wD///8A////AP///wD///8A////AP///wD///8AAAAAAP///wD///8AAALV3wAC1f8AAtX/AALV3////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////ADExMVaUlJTvmpqa/o+Pj/9/f3//bGxs6f///wD///8A////AP///wD///8A////AP///wAAAAAA////AP///wAAAtXfAALV/wAC1f8AAtXf////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////ADIyMlaOjo7vk5OT/o+Pj/99fX3/XmBe7RQvFE0TLhRHCxUJGwIEAgH///8A////AAAAAAD///8A////AAAC1d8AAtX/AALV/wAC1d////8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////ADAwMFaIiIjviYmI/k9yS/85lzv/OqRG/zmkRv81mDn3LGImogsUCRX///8AAAAAAP///wD///8AAALV3wAC1f8AAtX/AALV3////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////ACwsLFhJdUT7VKla/223fv94vIn/cLqF/2W2e/9Lp1L/NHEruwYKBAYAAAAA////AP///wAAAtXfAALV/wAC1f8AAtXf////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AGDETTUCmUP5DrF//OalV/ziqV/85qlr/Oqtc/z+uY/89pU3+GjQVTAAAAAD///8A////AAAC1d8AAtX/AALV/wAC1d////8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wAmWyaPOKlV/jmqWf46rF3/Oq5g/zuvY/87r2T/O7Bl/juuYv4oXCeJAAAAAP///wD///8AAALV3wAC1f8AAtX/AALV3////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////ACZkMJk6rFz/O65h/zywZv8/smv/RLNw/0i0c/9JtXT/R7Ry/y1mN5IAAAAA////AP///wAAAtXfAALV/wAC1f8AAtXf////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AHEklajuvZP8/smv/SbV0/1S4fP5duoP/YruH/2O7iP9huob/JUotYgAAAAD///8A////AAAC1d8AAtX/AALV/wAC1d////8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wAJFAkUOZlc3lC3ev9guoX/bb2P/na/lv97wJv/fMCc/2KgetkMFQwQAAAAAP///wD///8AAALV3wAC1f8AAtX/AALV3////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wAUKhgxTpZo0XW+lf6DwqH+jcWp/5LGrf5tnoHOGy0dLf///wAAAAAA////AP///wAAAtXfAALV/wAC1f8AAtXl////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wAHDQgJITonRj9gS3RDYU50JjwsRAgQCQj///8A////AAAAAAD///8A////AAAC1eUAAtX+AALV9QAC1f0AAtUR////AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP///wAAAtUQAALV/QAC1fYAAtXGAALV/wAC1Xb///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AAAC1XIAAtX/AALVxwAC1VUAAtX+AALV+QAC1XYAAtUR////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AAAC1RAAAtVyAALV9wAC1f8AAtVZ////AAAC1XsAAtX+AALV/wAC1f0AAtXlAALV3wAC1d8AAtXfAALV3wAC1d8AAtXfAALV3wAC1d8AAtXfAALV3wAC1d8AAtXfAALV3wAC1d8AAtXfAALV3wAC1d8AAtXfAALV3wAC1d8AAtXoAALV/QAC1f8AAtX/AALVgP///wD///8A////AAAC1VUAAtXGAALV9QAC1f8AAtX/AALV/wAC1f8AAtX/AALV/wAC1f8AAtX/AALV/wAC1f8AAtX/AALV/wAC1f8AAtX/AALV/wAC1f8AAtX/AALV/wAC1f8AAtX/AALV/wAC1f8AAtXzAALVxwAC1Vn///8A////AA=="
  },
  SQL: {
    type: "Stored Query",
    id: 29,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AIxcOASIXDgouHhMjQSkaRkovHl1TNCJmUzUiZUguHlk/KRtALB4THSYaEQj///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AJhkPD0UrG1tvSDCroGtK5L+DXP7GjWX/y5Rq/82Xbf/Nlmz/ypJp/8SLY/+8gVv8mWZH3GpFL59DLB1NKh0TCv///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AKBoQDVAyH3mZXz/ltndS/7x/Wv+/hF7/wohi/8OJYv/DiGL/xYxl/8SKZP/Ch2H/wodh/8CFX/+8gFv/uHpV/7NzT/+SXD7aTDIhZzEgFQj///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////ADMgEzeFTjDUqmZA/65sR/+zc07/w4tj/9Kif//fu57/7NTA//Xn2v/15dj/8NnF/+nJrP/etI3/06Bz/8WMY/+5e1T/rmxH/6tnQv+oZD7/f08zxTclGCf///8A////AP///wD///8A////AP///wD///8A////AP///wA3IhRJllMt8KJaM/+takP/wode/9ajdv/aqX3/1qeA/9Skf//SoHr/0Z10/9Gccf/RnHH/0p50/9Ofdf/UoHT/059z/86Ybv+/hF7/sG9J/6RdN/+eVS3/k1Yy5jglGDb///8A////AP///wD///8A////AP///wD///8ALx0RLpBLJ+6dUyr/sXBK/8GGYP/DiWL/voNd/76CXf/Bh2D/xYtk/8ePZ//JkWn/ypJq/8qSaf/IkGj/xo1m/8OJ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gP/Om3//zJh8/8iSc//Dimb/v4Nd/7Z3Uf+XSSH/ZEYuiP///wD///8A////AP///wBaNB6cpmA6/7FxTP+zc0//tXZS/7d5VP+5fFf/u35Z/72BW//BhmL/yJJ0/82af//OnID/z52B/9Cegv/Qn4L/0aCD/9Ggg//RoIP/0aCD/9Ggg//Qn4L/0J6C/8+dgf/Llnf/wohj/65rRP9qRCml////AP///wD///8A////AFkzHZ2xcEv/tHRP/7Z3Uv+4elX/un1Y/7yAWv++g13/xo9v/82af//PnYH/0J+C/9Ggg//SoYT/06KF/9Sjhv/UpIb/1KSH/9Wlh//UpIf/1KSG/9Sjhv/TooX/0qGE/9Ggg//Om3z/wYdg/2VAKJ7///8A////AP///wD///8AUDMhebR0UP+2eFP/uHtW/7t+WP+9gVv/v4Re/8mUdf/PnYH/0J+C/9KhhP/To4X/1KSH/9WmiP/Wp4n/1qiJ/9epiv/XqYr/16mK/9epiv/XqYr/1qiJ/9anif/Vpoj/1KSH/9Ojhf/Kk2//Y0cxd////wD///8A////AP///wA0Ixc7tndS/rl7Vv+7fln/voJc/8CFX//HkG7/0J6B/9Kgg//To4X/1aWH/9aniP/XqYr/2KqL/9mrjP/arI3/2q2N/9qujv/aro7/2q6O/9qtjf/arI3/2auM/9iqi//XqYr/1qeI/8uYc/xBMiMv////AP///wD///8A////AC0fFAaCVzzDu35Z/76CXP/AhV//wohi/86bfP/SooT/1KSG/9aniP/XqYr/2auM/9qtjf/br47/3LCQ/9yxkf/dspL/3bKS/92zkv/dspL/3bKS/9yxkf/csJD/26+O/9qtjf/Yq4v/hGNJsD0uIAP///8A////AP///wD///8A////ADYmGTKsdVPuwIVf/8KJYv/GjGX/0Z+A/9Wlh//WqIn/2KuL/9qtjf/bsI//3LGR/92zk//etZT/37aV/+C3lf/guJb/4LiW/+C4lv/gt5X/37aV/961lP/ds5P/3LKR/7iQcOJCMyUh////AP///wD///8A////AP///wD///8A////AD0qHESpdVPpxYxl/8iQaP/QnXn/16mK/9msjP/br47/3LGR/960k//ftpX/4LiW/+G5l//iu5n/47uZ/+O8mv/jvJr/47ya/+O7mf/iu5n/4bmX/+C4lv+yjm7aRjcoL////wD///8A////AP///wD///8A////AP///wD///8A////ADMkGCR2UTmuxIxl+86Ybv/WpoP/27CP/92ykv/ftZT/4LiW/+K6mP/jvJr/5L6b/+XAnP/mwZ3/5sGe/+bBnv/mwZ7/5sGd/+XAnP/Wr4z2dl1Hlj8yJRX///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////ADAiFwM4KBs1aEkzlaZ5Vt3SoHn93rOO/+G5l//jvJr/5b+b/+bBnv/nwqD/6MSj/+jFpP/oxqX/6Mam/+C7m/usjXLSa1VChD0wJCU8MCMB////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8ALyIXCTYnGyhROylYZEw4fXBZRZiCaVSoinJdsIt0X7CFb1yodWFQl2pXR3pUQzVROS4jITYrIQb///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  THM: {
    type: "Theme",
    id: 62,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AHN2MzlydTNQcXMzBf///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wB5ezSKdXk0/3R3M/9zdjOe////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AHt+NriIizn/en00/3Z5NPD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AtbW2D7W2tYCzs7O7s7OzrbKzslH///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AfoE3bYeLOP98fzb/en007////wD///8A////AP///wD///8A////AP///wD///8A////ALi5uBq3uLfXvb69/8PDw//BwcL/t7e4/7Ozs4r///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wCBhDcdgoQ4/4CCN/99gDa0////AP///wD///8A////AP///wD///8A////AP///wC6u7oaubu62MLExf/Ozs//zc7N/8vMzf/Jysv/uru6/7Ozs4v///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AIOHOAOEhzj/g4Y4/4GEN1H///8A////AP///wD///8A////AP///wD///8AvLy9Gru7vNjGx8b/0dHS/9DR0P/Ozs//zc3O/8zNzP/e3t//yMjI/7Ozs4v///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AiIs5B4iLOf+GiTjzhIc4Bv///wD///8A////AP///wD///8A////AL6/wBq9vr/YycrJ/9XV1f/S1NP/0tPS/9DQ0f/P0M//4eHh//b19v/08/T/yMjI/7Ozs4v///8A////AP///wD///8A////AP///wD///8A////AP///wCMjzsNjI87/4qNObv///8A////AP///wD///8A////AP///wDAwMEav8DB2MvLzP/Y2Nn/1tbX/9XV1v/U1dT/0tPS/+Pj4//29fb/9vX2//b19v/08/T/yMjI/7Ozs4v///8A////AP///wD///8A////AP///wD///8A////AI+TPBOPkzz/jpE7jf///wD///8A////AP///wD///8AwsPDGsLDwtjOzs//29vc/9ra2v/Y2Nn/19fX/9XV1v/l5eX/9/b3//f29v/29fb/9vX2//b19v/08/T/yMjI/7Ozs4v///8A////AP///wD///8A////AP///wD///8AlJc9GJSXPf+RlTtq////AP///wD///8A////AMXGxxrExsXY0dHS/9/e3v/d3d7/29vc/9ra2//Z2dn/5+bm//j39//39vf/9/b3//f29//29vf/9vX2//b19v/08/T/yMjI/7Ozs4v///8A////AP///wD///8A////AP///wCYmz4fmJs+/5WZPU////8A////AP///wDGx8Yax8jH2NTU1f/j4eL/4ODh/9/f4P/e3d3/29vc/+no6P/49/f/+Pf3//j39//39vf/9/b3//f29//39vb/9vX2//b19v/08/T/wcHC/7Ozs4v///8A////AP///wD///8A////AJyfPyabnj//mJs+PP///wD///8Av8G7Gru8tNjGx73/5OTl/+Pi5P/j4eL/4ODh/9/f4P/r6ur/+Pf3//j39//49/f/+Pf3//j39//49/f/9/b3//f29//39vb/9vb3/+Li4//Jysn/ubq5/7Kzsov///8A////AP///wD///8An6JAKp2hQP+coD8u////AMDBtxqwsp3YjpBi/+Tj4v/m5uf/5eXl/+Pi5P/i4uP/7Ozt//n4+P/5+Pj/+Pf3//j39//49/f/+Pf3//j39//49/f/9/b3//f29//k5OX/zM3O/8rLzP/Iycj/ubq5/7Kzsof///8A////AP///wCipUEvoKRB/6WoTyXAwrEatbef2ICDO//V1Mj/6Ojp/9/e2//m5uf/5eXl/+/t7v/5+Pj/+fj4//n4+P/5+Pj/+fj4//j39//49/f/+Pf3//j39//49/f/5ubm/8/P0P/Nzs//zM3M/8rLyv/Hx8j/tre2/rKzsjb///8A////AKOnQjWkp0L/sbRzL77AqtePkkH/iIs5/8TFp/+lp3b/k5Vc/+fn6P/x7/D/+/f6//v3+v/5+Pn/+fj4//n4+P/5+Pj/+fj4//j39//49/f/+Pf3/+jn5//S1NP/0dLR/8/Qz//Nzs3/y8zL/8nKyf++v77/s7Ozf////wD///8Ao6lGN6OpRP+6vZGknqJL/5aaPv+SlT3/jpE7/46RRP/Q0Lz/8vDx//v5+v/7+fr/+/f6//v3+v/79/r/+fj5//n4+P/5+Pj/+fj4//j39//q6en/1tbW/9TV1P/S09L/0NHQ/87Pzv/Mzc7/ysrL/7/Av/+zs7N+////AP///wClrEs3pKpK/6muV+mhpkP/r7hp/6ClSf+vsW//4+Lb//Px8v/7+fr/+/n6//v5+v/7+fr/+/n6//v3+v/79/r/+fj5//n4+f/5+Pj/6+rq/9nZ2v/X19j/1dXW/9LU0//R0dL/z8/Q/83Nzv/LzMv/ubq5/rS0tTP///8A////AKauTzWmrk7/pq9R/6u0W/+zvG3/u757/+7s7P/08fP/+/n6//v5+v/7+fr/+/n6//v5+v/7+fr/+/n6//v5+v/79/r/+/f6/+7s7f/c3N3/2trb/9jY2f/W1tf/1NTV/9LT0v/Q0NH/zs/O/76/vv+3uLeA////AP///wD///8AprBRDKavU/Spsln/sbxt/6y2X//n5tr/9PP0//v5+v/7+fr/+/n6//v5+v/7+fr/9/b3/9va2v/X1db/8vDx//v5+v/u7u//4N/f/97e3//b29z/2dna/9jY2P/V1db/1NXU/9HS0f/AwcL/ubq7g////wD///8A////AP///wD///8AqLJWgaawVf+xvG3/rbhm//X09f/8+fv/+/n5//v5+v/7+fr/+/n6//Tz9P+rqqr/pqWl/6uqqv+hoKD/3Nva/9LRwf+8vqD/qauE/5eZbP+HiVr/enxO/3p8Vf+Ym4L/v8G//7q6u4P///8A////AP///wD///8A////AP///wCnslcEqLJZs6mzWv+yvXH/3+Db//v5+v/8+/v//Pr7//z6+//8+fv/zszM/6ysrP/j4uL/6Ojp/8LBwf+Zmn//lJdC/5yeX/+mqHv/r7GR/7S1nv+xsp7/nqCH/2tsQv92eVS1////AP///wD///8A////AP///wD///8A////AP///wCoslkFqLJZnKu1XP/AxZ3/4uLi//v5+v/8+/v//Pv7//z7+//DwsL/v76+/+zs7f/x8PD/2tnZ/6Wlo//i4+H/4+Lj/+Hh4v/f3+D/3dzc/9ra2//IyMj/m52MolteK8T///8A////AP///wD///8A////AP///wD///8A////AP///wD///8Ap7JXVaiyVebAxJ/94uLi//v5+v/8+/v//Pv7/9zb2/+joqL/4N/f/+rp6v+ysbH/vLu7/+bm5v/k4uP/4+Hi/+Dg4f/d3d7/ysvK/7W2soN2eVRKW14rmP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AqLJXDau0YH/Dx6ja4uLi//v5+v/8+/v/+/n6/8nIyP+fnp7/nJub/7a1tf/k5OX/5ubn/+Xk5P/j4uP/4ODh/83Nzv+xs6eFf4FYVl5hLbxbXisT////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AL7DnQXR08+Z4uLi//v5+v/19fX/7+3u/+3r7P/q6uv/6urr/+no6P/n5+j/5eXm/+Pi4//Pz8//nqB893N2Ntxnay+GYmQsCf///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////ANLT0gHS1dOZ4ODg/+/v8P/v7u7/7u3t/+3r7P/s6uv/6enq/+fn6P/l5eb/0dHR/6GjesmChUJxdHg1E////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////ANLU0wHS1dOZ3d3e/+/u7v/v7e7/7ezs/+vr7P/q6er/5+fo/9LT1P/IycaD////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////ANLU0wHS1NOZ3d3d/+/t7v/u7O3/7Ovr/+rp6f/V1db/zc7Ng////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////ANLU0wHS1NOU2NjZ/+Hh4v/f3+D/1NTU/s7Oz4D///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wDS09I+0dHShtDQ0YTPz9A3////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  TVD: {
    type: "Time Varying Data",
    id: 141,
    icon: "data:image/png;base64,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"
  },
  WCOST: {
    type: "Distribution Cost Estimator",
    id: 170,
    icon: "data:image/png;base64,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"
  },
  WINF: {
    type: "Distribution Inference",
    id: 128,
    icon: "data:image/png;base64,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"
  },
  WKSP: {
    type: "Workspace",
    id: 137,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AIaCggKFgYFLhICAXIN/f1yCfn5cgX19XIB8fFx/e3tcfnp6XH15eVx8eHhce3d3XHp2dlx5dXVceHR0XHdzc1x2c3NcdnJyXHVyclx1cXFcdXFxXHVxcVx1cXFQdXFxBv///wD///8A////AP///wD///8A////AP///wD///8Aqohh77yITP+8iEv/u4ZJ/7uGSP+6hEb/uoRF/7mDRP+3gUP/toFD/7R/Qv+xfUH/sX1B/7B9Qf+ue0D/rXtA/6t5P/+qeD//qng//6h3Pv+odz7/qHc+/6h3Pv+ZdU33////AP///wD///8A////AP///wD///8A////AP///wC1iVf+4My2/+PWyv/e0MH/3tDB/97Qwf/e0MH/3tDB/97Qwf/e0MH/3tDB/97Qwf/e0MH/3tDB/97Qwf/e0MH/3tDB/97Qwf/e0MH/3tDB/+HUxf/n3dL/4syz/6R3Qv////8A////AP///wD///8A////AP///wD///8A////ALWLWv7gz77/39DB/9/Qwf/f0MH/39DB/9/Qwf/f0MH/39DB/9/Qwf/f0MH/39DB/9/Qwf/f0MH/39DB/9/Qwf/f0MH/39DB/9/Qwf/f0MH/39DB/+HTxf/iz7r/o3ZD/////wD///8A////AP///wD///8A////AP///wD///8AtYtb/uDRwf/g0cH/4NHB/+DRwf/g0cH/4NHB/+DRwf/g0cH/4NHB/+DRwf/g0cH/4NHB/+DRwf/g0cH/4NHB/+DRwf/g0cH/4NHB/+DRwf/g0cH/4NHB/+DRwP+jdkP/////AP///wD///8A////AP///wD///8A////AP///wC2jF3+4dLB/+HRwP/h0sD/4dHA/+HRwP/h0b//4dG//+HRwP/h0cD/4dHA/+HSwP/h0sH/4dLB/+HSwf/h0sH/4dLB/+HSwf/h0sH/4dLB/+HSwf/h0sH/4dLA/6N3Q/////8A////AP///wD///8A////AP///wD///8A////ALaNXv7j08H/5dXE/+XXx//m18j/5tfJ/+bXyf/m18n/5dbI/+XVx//k1MP/49PB/+LRwP/i0b7/4tG//+LSwP/j08H/49PB/+PTwf/j08H/49PB/+PTwf/j08D/pXdE/////wD///8A////AP///wD///8A////AP///wD///8At45g/uXUw//q3M3/697Q/+vf0f/s4NP/7eDU/+3h1f/u4tb/7eLX/+7j1//t4tf/7eDU/+vdz//o2Mn/5dPB/+TRvv/k0r//5dTB/+XUwf/l1MH/5dTB/+XUwP+leET/dJVxPGycastpnGfUZ5tl1GaaZNRlmWPUZJhi1GWZY9S2klb/6NfE/+3g0v/u4dT/7uLV/+/i1//v49j/8OXZ//Dl2v/x59z/8ufd//Lo3//z6uD/8+vh//Tr4v/y6N//7uLU/+jXyP/m0r//59TA/+fUwf/n1MH/59TA/6Z4RP9iqWH6Z71n/3TDdP9ywnL/ccJx/3DBcP9qv2r/X7pf/8CPV//q2Mf/7+LV//Dj2P/x5dn/8uba//Ln3P/y6N3/8+jd//Pp3//06uD/9Ovi//Xs4//17OT/9u7l//bu5//38er/9+/o//Ll2v/q2MT/6NTA/+jWwf/o1sD/qHpF/16uXf7O59D/1unY/9bp2P/W6dj/1unY/9bp2P/W6dj/x5pn/+3byf/y5tn/8+jc//To3f/16t7/9erf//Xr4P/16+L/9e3j//bt5P/27uX/9+/n//fw6P/38en/+PHq//jy6//58+3/+vbx//jx6v/u3s7/6tbA/+rWwP+pekX/Ya9g/tbq2f/W6tn/1urZ/9bq2f/W6tn/1urZ/9bq2f/FmWX/793L//Xp3f/16t//9uvg//bs4v/27eP/9+7k//fu5f/47uf/+O/o//jw6f/58ur/+fLr//nz7P/59O3/+fTu//r17//69fD//Pj1//v18f/w3sz/69e//6t8Rv9ir2H+1uvZ/9Xq2P/V6tj/1erY/9Xq2P/V6tj/1erY/8WZZf/x383/9+zh//ft4//37eT/+O7l//jv5//48Oj/+fHp//ny6v/58+v/+vPs//r07v/79e7/+/Xv//v18P/79vH/+/jy//z48//7+PT//fr4//jt4//t2ML/q3xG/2OwY/7W7Nr/2O7b/9nt3P/a7tz/2u7d/9ru3f/a7t7/x5pn//Phzv/47+f/+fDp//ny6v/58+v/+vPt//v07v/79e//+/Xw//z28f/79vL/+/jz//349P/9+fX//fn1//369//9+vj//fv4//77+f/+/Pv/+fDo/+7Zwv+sfUb/ZLFk/tfu2v/e8OH/3/Hi/+Dx4//h8uT/4vLk/+Pz5f/Hmmf/7djA//fq3f/47OH/+O3i//ju4//57uP/+e7k//nv5f/57+b/+fDn//nw6P/58ej/+vHp//ry6v/68ur/+vLq//ry6//68+v/+/Ps//ry6//26Nr/6dS8/65+R/9lsWX+2PDc/+Dz4//i8+X/4/Tl/+T05v/l9Of/5fXo/8KTXP/No3P/48Wm/+/Zwv/y3sv/8t/M//LgzP/y383/8uDN//Lgzf/y4M7/8+DO//Pgzv/z4M7/8+HP//Phz//z4c7/8+HP//Phz//y4M3/6dC0/9m2j//DlF3/sXxI/2eyZv7Z8dz/4/Tl/+X15//l9ef/5vbo/+f26f/o9ur/vYpO/8KSW//Kn27/yp9u/8mdbP/JnWz/yZ1s/8mdbP/JnWz/yZ1s/8mda//JnWv/yZ1r/8mda//JnWv/yJxq/8icav/InGr/x5to/8ebaP/Hm2j/x5to/8KTXP+0ekf/Z7Jm/trz3v/l9uj/5/fq/+j36v/p9+v/6vfs/+r47P+9ik7/0Kp+/9a1j//Usov/1LKL/9Sxiv/TsIj/06+H/9KthP/RrIL/0auB/9Cqf//Qqn7/zqd7/86nev/NpXj/zKN1/8yjdP/LoXL/y6Fx/8qfb//Kn2//zqd6/7R6R/9osmf+3PXf/+j46v/q+ez/6vns/+v57f/s+e7/7fnv/72KTv/PqX3/1LGK/9Kuhf/SrYT/0ayC/9Grgf/Qqn//0Kp+/86ne//Op3r/zaV3/8yjdf/Mo3T/y6Fx/8qfb//JnWz/yZ1r/8icav/Hmmf/xZll/8eaZ//Op3r/tHlH/2iyZ/7e9uH/6/ru/+z67//t+u//7vrw/+/68f/v+vH/voxR/8+pff/YuJX/17eS/9e2kf/WtY//1rWP/9W0jv/Vs43/1LGK/9Sxiv/TsIj/0q6F/9KthP/RrIL/0auB/9Cqf//Qqn7/zqd7/86nev/NpXj/zaV4/86nev+0eEn/arNp/t724v/v+vD/8fvx//H78//y/PT/8/z0//T89f/InGr/vIhL/8SWYf/ElmH/xJZh/8SWYf/ElmH/xJZh/8SWYf/ElmH/w5Vf/8OVX//DlV//w5Vf/8OVX//DlV//w5Vf/8OVX//DlF7/w5Re/8OUXv/DlF7/vIhM/7VtU/dqs2n+zO7Q/+f56f/p+uz/6vrs/+v67f/r+u3/7Pru/+fUvf/Rq4H/yp9v/8mdbP/JnWz/yZ1s/8mdbP/JnWz/yZ1s/8mdbP/JnWv/yZ1r/8mda//JnWz/w5Re/6+BQv+yaFnotWZZ6LVmWei1ZlnotWZZ6LVmWei1Yl3WtVZoM2qzav224Lb/9/v3//f79//3+/f/9/v3//T69P/v+O//4vLi/9Xt1f/O6s7/zOnM/8zpzP/M6cz/zOnM/8zpzP/M6cz/yujK/8royv/K6Mr/yujK/8royv+c1Zz/TqZO/////wD///8A////AP///wD///8A////AP///wD///8AabFp/WC6YP9gumD/X7pf/1+6X/9ful//X7pf/1+6X/9duV3/Xbld/1y5XP9cuVz/XLlc/1y5XP9buFv/W7hb/1u4W/9buFv/W7hb/1u4W/9buFv/W7hb/1u4W/9dsl3/////AP///wD///8A////AP///wD///8A////AP///wBns2f+f8l//5HQkf+R0JH/kdCR/5HQkf+R0JH/kNCQ/5DQkP+Oz47/js+O/47Pjv+Nz43/jc+N/43Pjf+Nz43/jc+N/4zOjP+Mzoz/jM6M/4zOjP+KzYr/gMmA/2K3Yv////8A////AP///wD///8A////AP///wD///8A////AGezZ/6Nz43/h8yH/4LKgv+CyoL/gMmA/3/Jf/9/yX//fsh+/3zHfP98x3z/e8d7/3nFef95xXn/eMV4/3jFeP93xHf/dcN1/3TDdP9ywnL/csJy/3TDdP+Mzoz/ZLZk/////wD///8A////AP///wD///8A////AP///wD///8AaLJo/o3Pjf+GzIb/gMmA/4DJgP9/yX//fsh+/37Ifv98x3z/e8d7/3vHe/95xXn/eMV4/3fEd/93xHf/dcN1/3TDdP90w3T/csJy/3HCcf9wwXD/csJy/4zOjP9ktmT/////AP///wD///8A////AP///wD///8A////AP///wBpsWn9is2K/57Wnv+c1Zz/nNWc/5zVnP+b1Zv/m9Wb/5vVm/+a1Jr/mNOY/5jTmP+X05f/l9OX/5XSlf+V0pX/lNKU/5TSlP+U0pT/k9GT/5HQkf+T0ZP/is2K/2a0Zv7///8A////AP///wD///8A////AP///wD///8A////AHSmdNpgumD/Y7xj/2S8ZP9kvGT/ZLxk/2S8ZP9kvGT/ZLxk/2S8ZP9kvGT/ZLxk/2S8ZP9kvGT/ZLxk/2O8Y/9jvGP/Y7xj/2O8Y/9jvGP/Y7xj/2O8Y/9gumD/cqhy6P///wD///8A////AP///wD///8A////AP///wD///8A////AI2NjVWNjY2BjY2NgY2NjYGNjY2BjY2NgY2NjYGNjY2BjY2NgY2NjYGNjY2BjY2NgY2NjYGNjY2BjY2NgY2NjYGNjY2BjY2NgY2NjYGNjY2BjY2NgY2NjV3///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  WNTMP: {
    type: "Distribution Digitisation Template",
    id: 151,
    icon: "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAFSElEQVRYw+WXTYwcVxHHf/Ved0/PzO7a++GveB1sQLEMEtiyJT4OKAhxQUKRs1qIZCTunJA4RAJOnDhx48THyYoSvFLs+GKJC0IiQiGKEiGvsBOQzJr1fmWT/Zid7un3qjjMznjW9q7XwRwQJZVarX5V9X//qnr1Gv7fRXb7MDNz9bCZfbler5/J8+xEltWOi8hElqUjQMPMUudcDRAzVFVL791WCHErxvBRCGGpqsJ8u93+oKrC22b27vT0RX0sgJmZq8+PjY3++Nixo18fHx9PnPOoGqqGGZgZANuPnc4ERKT/dE5wDlqtls3Pz9+5d2/h56r2q6mpF/SRAK5evf6zc+e++JM8b7qq0n6wpyHeO0Qi77zz7uWiKL7fA+EGdn7pwoXzP/W+7soyDuz46WgISgjC+fPnvpck/gc7GHj11SvpqVMn/zE5eXIyBH3y7T0hEwsLcwt37sx9amrqhY7r5k6+eeLEs5M92vejqgrhPSS+jWrct10IyjPPHD8KfKOfgmZz6KveJ9uL9kdprD5iPP81Y/lv0bDyBOkwvE9oNhtfAUgAGo38syHsv+jMjKb/Pb5xDpERhsobbOolRNy+7GM0siz7dJ+BJEkP75dCM0M7cwxnf4Ha17DsSwwlN7HqzhOlL03TQ30AWZaOxbi//KtGDsgbJM3TIG3EbeCHznLAXUM17NOH4b0fG2zDRvew4bFKcZtG9nfIDgNLYMuQHaGezuPK2X35UFWSxNf7NSAizW7f710DZpHx8Do+G8WqNSxugSSAx9cnObB2jZXkDCJ+Tz+qRozxPgDnXNpjYC9Jilka3AJ7DtqL4DIQv+0mo+7ukrb/Sic/+1gA23Okz4Dv5WdXo1hxaOMyMqxYa6Eb3GWYJH0WJBvn4PJlFpIziM/2YFLYRt4F0IutujuAZP3P5OVsN4kbHwKC4RGfQFqHpAFJRo1l0o0/0Rl5fk8GABsAoGFw0j0ooVxjdOMaWIRoXVMFiEAJtMA7SFNIPEOtN1jKvoCvje7BgoU+AFUt92IgXXuT2tbfuj3TC/5gvTgFVyIiZPo+2fqbVOPf2iU4gBWDNbDR9fwwgNBeYeTj67iooGA6AECta+HuqznDOaO+ep2ieQGfH3okCOdc0TMlhLglIv2Lx6D6lRtIaw4tjdgBKwy21UqgNGhvvxfdNVoasvUv/PKNR/oUgU6n2uwzEEJYFoEYd/JqpsSVWdbKnMIZiRnODDH6CmCyPWgENAhBhFKFYuUm7nBA3MMzQlU/7AOoqs6Cc90hMShVVbGUTxGKD8g7qwz5DjUfSUVxdHfSy2lEqNRRRs+m1ijcKEntMxzpVKTpzpb0XqiqzkIfwOZm63aWJQ8xAMLIxCnC0ARWbVLFNtEqxCJY6N/nDEASTDxRamQ+J0ubpPkwIA/5TVPP1lb7/T6Adrv4Q4wdMzPZ2YpCnjcgbwBH+KSiA0dst9Y6VhTlH/sAVO2tu3fn3hsdPX52dbX1iQPtRw4ebDA/P38b7C3Y7oJLl75ji4uLP6zVYtVs1h5ZuU9D8zxleNjpvXsLL09Pv6hdjgfkypXXv3v69HO/qdcPNJeXNymK6j++mosIeZ4yMTFECK3y1q3bP7p48du/vJ/kB+S112ZONpvNl48dOzo9MjI6nmU1Op1IVSkhKKpKb3T3sO38EXEkiSNNHVnm6XRK1tc/Xl1cXJpptTZ/MT394q0dAHdD/sorv0uBz3vvPpfn+bP1ev2IczKWJOlImiapqnlVzaF7qjknMYRQVVW1rmqr7XaxWJbFP2PUWRFuvvTSdPVfLa7/Wfk3U5UzKAShDCIAAAAASUVORK5CYII="
  },
  WVAL: {
    type: "Distribution Validation",
    id: 127,
    icon: "data:image/png;base64,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"
  },
  VAL: {
    type: "Collection Validation",
    id: 108,
    icon: "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAABGdBTUEAALGPC/xhBQAAACBjSFJNAAB6JgAAgIQAAPoAAACA6AAAdTAAAOpgAAA6mAAAF3CculE8AAAABmJLR0QA/wD/AP+gvaeTAAAGvElEQVRYw8WXa2wcVxXHf2ceu157vU6860ea2o7dxGkhPBIJqYpVESVt2pICH5CQQhsqhBCIChVVQlURqKCiqJWoiEABUUEKVIgqgIr40iaQEEBJGtQUJCCBNHEd49iOHbPuvnd27j18mF3Hr8RuQeJoR3vmzsy9//P6n3tFVfl/ijf/5sCBg1va29tPep6XAlUFQQFUVRFQFBRU0PooiKqi0SMxxoTVavVYEARfPnXq5F8OH/6ZXTUAwOvs7Ejt3r0TVZXGoILIKnSAyyOj3vHjv787DEMduO22J3ft2v36sWNHw1UCUECxVglqFquNUUWi+W+qo1AJQta0pdz1t3TfE9ZqZuvWrd/YufPus8eP/7a2IgCt+1cVCY2qsdHsqqoiK+vWWgkCQ6wprhs29LmI3Kdgtm7l6R07dp09ceJYsFIImDOqYRogIivqcP19z3EllWploL/PRXWPquq2bdueGRq66+zJk38MbgLgf1MRpXKJ8fEJjDF4vuem0+0PVCplzWQ6Hgcu3DwEqlFoFW1YFblabqrX0UuiuZl4okUvj02IWovjOJrOZNwgqD0wOjryY8/zLodhWL2ZB95xCESEtrY13HHHFilXylhr8T1HUskE5VLJy+VySWNMQkSCegkv8sB/EQYRIfvGBSZ+cghiMbr2fYpEZxeeC81NPr7vN4rWmf/dghsahBJVo14f1hX17MibemX/10kPv0H7P/7OlYMHSCQSNCUSGm+K47oushT3QgD12d52CEqzWca//ay0l4tUKhUcIMzlEBFEHBFxuJEs8sACw1clJqxx5fkfkBwbJbQWz/OYKpfp3vtQPakXGLeSB+oI3kYIrp74HZz6A74XpVPVGGL33E/n0AcxVrFWo09UWa7xLZMDuuoQFKen5Nqh75Npa8OEIa7jkOvtZ/3eh8FxUVVsvafcqOk6i9ZfVsIgwNSWUvnl732H3tYkobXE4nGmxOHWzz9KLJnEGsWYqK9E8y4/+ZIQ1IloLgRTx37D+U98jPP7Ps7EkZexNmpRk2dOkzj/N2KJBK7jMFsuk9r7MKm+AYxRNVYJIxBab9fLykIiUkVkYRVMvfgC3Z0duL7PzI+eo5bPSfeejzD5/HO8p6eHShBgrKV4+xYGd93biLuogrGKpyIgiOgqAMCSRPE6uginJ7G+zy29vUz+6hec/9OrdAZVJJ7GqdX4VyVg3Sc/g7jenNuNteRzFYwxVEo+pVINWEoF3uLFtdHm672g67OPMPbUV+kOAmxLC30D/ZRzOVI9PRhjmcnOEr/vwyTX96oxKtYqE+N5PXq0IpOTFs9xgDKl0iDtmf0PFstH/np14lD2hh5gURWs6duAeeJJxp99mp58HtIZUh2diFpsJc9YrIlNH/ooxqqoVc6dy/LLnxdlcFML73+vh1O32WoTmzbdee+p05s3X7q4+0Hg1DJVsDBZVBW1ypoNA6z70lcYtVCezQKKqHJpdJTMQ5/GiSUwxjI+/haHX5xl82Ac3zcUClVy+egqFKr4vtGh7a19/QMbX9g4+M0Ny1dBY3upqjZKKKxVTa3voeuxJ7hQKFHN5Shks8z2bWTt+z6AMUoYWj3ySpZ0u1AqVcnlKstdUipVGdwUG0int30xmdwii6ogMg5ALWIV1CpWEatK67oeOr7wOH/+4UGsKrd+7hEa7+TzJbl4MU+mvYnZ2VqjqAjDaFPsec7cDlYVkq1yf7L13V9bJgmj7LP1MooAKNZGz1v7N9Ly1Leuj5vov1AM+Pe1ItgalYohX6hRKobRHAqeKzS3eCSTPokmF7XVXs9LJpfuB1RVVcVaVWtUosVVrVWxSoPb5+lIxHZWs9mcTE8vfwyoBVAuozPX5i2FWUpERHsLXAfxXEFVsE5ELA1ub3S5BhBVZe2ahGQ6XMamauDIXDKLLKB4AVRUxQnNaFibKSwNgaq6jkhLs6fNER/Uf9f3h/MIJToZAZpp0qGhjPz0lQnCZMuNAADgF4v4ucLLhfy5txaHwExPX6u89NKvE42jWH1RqYeHxePz2FPakiXa48JYYi21ZOuS/AbUL+SJz1wdzs2+fqBYvKQLAJRLxQuvvTZy5+nTJ7vL5VJiMfKF94u5Pbr3/Hdtbu7Y81ih7/auyto01o8pIE4toCk7I8krwyNhfnjfm8PfHYH6wXK+xGJxJwxrzUBsnqtv2M0Wg0mnOxPr+ofuqrbseNT6HYN4XisohCbv1qYutARnnvHt+NEzr54owjJUHARVCxR4h7J9+/akiZt/Bonp/dbVtOK2oCBeWPT8qZmY5MfcoDZn2H8A73lOCRbxj8EAAAAldEVYdGRhdGU6Y3JlYXRlADIwMTgtMTEtMDZUMDk6MzI6NDMrMDA6MDCNDgOGAAAAJXRFWHRkYXRlOm1vZGlmeQAyMDE4LTExLTA2VDA5OjMyOjQzKzAwOjAw/FO7OgAAAABJRU5ErkJggg=="
  },
  CGDT: {
    type: "Custom Graph",
    id: 172,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AJycnDCcnJx8nJycfJycnHycnJx8nJycfJycnHycnJx8nJycfJycnHycnJx8nJycfJycnHycnJx8nJycfJycnHycnJx8nJycfJycnHycnJx8nJycfJycnHycnJx4nJycI////AP///wD///8A////AP///wD///8AJycnDScnJ6InJyf6Jycn/ycnJ/8nJyf/KCgo/ygoKP8oKCj/KSkp/ykpKf8pKSn/KSkp/ykpKf8pKSn/KSkp/ykpKf8pKSn/KSkp/ygoKP8oKCj/KCgo/ycnJ/8nJyf/Jycn/ycnJ/YnJyeOJycnBf///wD///8A////AP///wAnJyeuJycn/ycnJ/8nJyf/KSkp/yoqKv8rKyv/LCws/ywsLP8sLCz/LCws/ywsLP8sLCz/LCws/ywsLP8sLCz/LCws/ywsLP8sLCz/LCws/ywsLP8rKyv/Kioq/ygoKP8nJyf/Jycn/ycnJ/8nJyeO////AP///wD///8AJycnICcnJ/4nJyf/KCgo/yoqKv8rKyv/LS0t/y4uLv8vLy//Ly8v/y8vL/8vLy//Ly8v/y8vL/8vLy//Ly8v/y8vL/8vLy//Ly8v/y8vL/8vLy//Ly8v/y4uLv8sLCz/Kysr/yoqKv8oKCj/Jycn/ycnJ/YnJycI////AP///wAnJyc+Jycn/yYmJv8nJyf/Kysr/y4uLv8vLy//MDAw/zExMf8xMTH/MTEx/zExMf8xMTH/MTEx/zExMf8xMTH/MTEx/zExMf8xMTH/MTEx/zExMf8xMTH/MDAw/y8vL/8tLS3/LCws/yoqKv8nJyf/Jycn/ycnJx7///8A////ACcnJz8nJyf/IyMj/zExMf9JSUn/MjIy/zExMf8yMjL/MzMz/zMzM/80NDT/NDQ0/zQ0NP80NDT/NDQ0/zQ0NP80NDT/NDQ0/zQ0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tP/t7e3/6+vr/7i4uP+dnZ3/m5ub/5qamv9NTU3/KSkp/ycnJx////8A////ACcnJz8pKSn/bGxs/6Wlpf+mpqb/p6en/6ioqP+oqKj/qamp/6mpqf+pqan/qamp/6mpqf+pqan/qamp/6mpqf+pqan/qamp/6mpqf+oqKj/qamp/8rKyv/z8/P/5+fn/7a2tv+mpqb/paWl/1lZWf8oKCj/JycnH////wD///8AJycnPygoKP96enr/sLCw/7Gxsf+xsbH/srKy/7Ozs/+zs7P/s7Oz/7Ozs/+zs7P/s7Oz/7Ozs/+zs7P/s7Oz/7Ozs/+zs7P/s7Oz/7Ozs/+ysrL/tra2/9ra2v/19fX/4eHh/7e3t/+wsLD/ZmZm/ygoKP8nJycf////AP///wAnJyc/KCgo/4iIiP+6urr/u7u7/7u7u/+8vLz/vLy8/729vf+9vb3/vb29/729vf+9vb3/vb29/729vf+9vb3/vb29/729vf+9vb3/vb29/729vf+7u7v/wsLC/+Xl5f/39/f/4ODg/8DAwP9zc3P/KCgo/ycnJx////8A////ACcnJz8nJyf/mJiY/8TExP/ExMT/xcXF/8XFxf/Gxsb/xsbG/8bGxv/Gxsb/xsbG/8bGxv/Gxsb/xsbG/8bGxv/Gxsb/xsbG/8bGxv/Gxsb/xsbG/8bGxv/FxcX/zs7O//Hx8f/29vb/1dXV/4ODg/8nJyf/JycnH////wD///8AJycnPycnJ/+pqan/zs7O/8/Pz//Pz8//z8/P/9DQ0P/Q0ND/0NDQ/9DQ0P/Q0ND/0NDQ/9DQ0P/Q0ND/0NDQ/9DQ0P/Q0ND/0NDQ/9DQ0P/Q0ND/0NDQ/8/Pz//Pz8//3t7e//b29f/b29v/kpKS/ycnJ/8nJycf////AP///wAnJyc/Jycn/7Ozs//X19f/19fX/9jY2P/Y2Nj/2NjY/9jY2P/Y2Nj/2NjY/9jY2P/Y2Nj/2NjY/9jY2P/Y2Nj/2NjY/9jY2P/Y2Nj/2NjY/9jY2P/Y2Nj/2NjY/9jY2P/Z2dn/3t7e/9nZ2f+bm5v/Jycn/ycnJx////8A////ACcnJycnJyf/kpKS/+Dg4P/g4OD/4ODg/+Hh4f/h4eH/4eHh/+Hh4f/h4eH/4eHh/+Hh4f/h4eH/4eHh/+Hh4f/h4eH/4eHh/+Hh4f/h4eH/4eHh/+Hh4f/h4eH/4eHh/+Dg4P/g4OD/4ODg/3l5ef8nJyf6JycnDP///wD///8A////ACcnJ8E3Nzf/p6en/+Hh4f/o6Oj/6Ojo/+jo6P/o6Oj/6Ojo/+jo6P/o6Oj/6Ojo/+jo6P/o6Oj/6Ojo/+jo6P/o6Oj/6Ojo/+jo6P/o6Oj/6Ojo/+jo6P/o6Oj/6Ojo/93d3f+bm5v/Ly8v/ycnJ6L///8A////AP///wD///8AJycnGScnJ8EnJyf/Jycn/ycnJ/8nJyf/KCgo/ygoKP8pKSn/KSkp/ykpKf8pKSn/KSkp/ykpKf8pKSn/KSkp/ykpKf8pKSn/KSkp/ykpKf8oKCj/KCgo/ycnJ/8nJyf/Jycn/ycnJ/4nJyeuJycnDf///wD///8A////AP///wD///8A////ACcnJycnJyc/JycnPycnJz8nJyc/JycnPycnJz8nJyc/KCgoPygoKD8oKCg/KCgoPygoKD8oKCg/KCgoPygoKD8nJyc/JycnPycnJz8nJyc/JycnPycnJz8nJyc+JycnIP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  DMGFUNC: {
    type: "Damage Function",
    id: 199,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAGGkuipJteiLRbjxzUW58+5FufT3Rbn090W59PdFufT3RLn090K59PdCufT3Qrj090G39PdBt/T3Qbf090C39PdAuPT3QLj090C49PdAuPT3QLj090C38+xAtvHJQrLngleeqx8AAAAAAAAAAAAAAAAAAAAAAAAAAAD//wFLsd16P7v59z3A/v9fyP//bc3//3HO//9wzv//cM7//3DO//9wzv//b87//2/O//9uzv//bs3//27N//9uzf//bs3//23N//9tzf//bc3//23N//9tzf//Z8v//1fG//83vv/+PLn48UKs2W8AAAABAAAAAAAAAAAAAAAAUrPdgTy9/P5ny///reP//63j//+k3P//oNv//5zh//+W4///m97//5ff//+T4f//md///5vZ//+a2f//mNn//5fe//+P4P//kt3//5Tc//+N3///kt7//5bY//+a2P//puD//6Pf//9ax///NLv8/USt2HAAAAAAAAAAAFupyTpAvvv6bc3//6/k//+Q2f//g9T//3zS//9w1///jr3M/86WS//diyn/2o4x/6qsi/9nz///Zcz//2jM//9gy///Zsn6/7ehcv/ejCz/340q/8qXU/93utX/Usj//1zJ//9iy///fNL//6Tg//9bx///O7r59FOWuykAAAAASrfsqEfD/v+v5P//lNT8/7ukdP9+0Pf/ctb//6eumP/gjCj/tKd//4fA1P+as7T/15I7/86XTf91xOb/WtD//4G3zP/akTn/zZdN/4W4w/96vNH/tKN0/+WNKf+UrKD/Ssv//2u53f+qpYH/cM///53d//84vv7/QrLokgAAAABHuvTscM7//6Pd//+QzO3/0pRE/96NLP/bjTD/248y/5G/y/9r2P//hb3a/3bL9P9m0f//wqFi/+KMKv/fjy//5Iwq/66ng/9R0///bsPo/3W63P9O0f//hbK+/+GQL//ekTX/5o0p/76cYv9Yx///jtX//1rH//9At/HWAAAAAEK//f6G0///m9v//4TU//943P//mb/P/5u7wv902f//o7Kq/92PMv/fjCz/4Iwq/8GhZP9rz///fMTi/5C2v/9ux/L/bsfu/86XTf/jjSv/440s/96QNP+JsLj/V8v//4qxsf9wvNr/R87//1nG//970P//bMv//z+59fkAAAAARMD+/4nU//+V2///js3v/8+WSv+Tx9r/iM/x/76lbv/djS7/pbGf/3fR/v+Kw9b/zJhR/9qROf+RtL//bcz8/5yvpv/hjSz/vKJq/3LE6f9jyfz/nquW/+SMKv+ypHj/XMj9/4WxvP/ImVX/UcX//3DO//9ozP//Prr3/AAAAABDwP7/itX//5fb//+Oz/b/xZ9k/96MKv/diyv/0pRG/4bM7P9/0fj/mrm0/43C0v9p2P//ramF/+GMK//gjCz/3o4x/52vqP9a0///irbE/4+zsv9jyv7/c8Hj/9eUPf/kjSz/5Iwq/6iohv9Sxf//cM7//2jM//8+uvf8AAAAAEPA/v+I1P//mNv//4rW//9/3v//jdHy/4/L5f963P//squF/9+MKv/ajzb/340r/9KURf99yu3/btH//4S+2f9j0///irzJ/9uSNv/gji7/3JA0/+KOKv+iqZD/UtL//3W/3P9hyPv/Ts3//1nG//9xzv//aMz//z669/wAAAAARcH+/4PV//+g3P//lszn/9iNL/+nt7T/nMPK/8yYUv/XkDv/m73J/3Xa//9+0Pn/vaZy/9+NLP+mrpj/h8HV/62og//ijCj/qquQ/2jO//9c0f//jLXA/92QNP/Fnlr/fL3S/52rmP/Ykjz/VMf//3LP//9uzP//Prr3/AAAAABEwf7/hNX//5zd//+S2///s7CM/9qMMP/cjCv/w6Jq/4fS+f+C2f//f9P//3zT//9z2f//oLWr/9iSO//ijSr/0ZZJ/4+6y/9m0v//a8z//2nL//9g0P//a8fz/8OcXv/ljSj/25E4/42ysv9ZyP//c8///2nM//8+uvf8AAAAAETB/v+K1f//o97//5La//+P3f//idr//4nY//+D2///hdX//4PU//+G2v//ht3//4Pg//994f//dOL//3vd//9v4P//c9z//3XZ//9x1P//a8z//2nM//9ly///Xc///2LL//9bzv//W8n//17J//96z///b8z//z669/wAAAAARMH+/4XV//+k3v//k9r//5HZ//+P2P//i9f//4nW//+H1f//itz//1uTsf8AAAD/AAAA/wAAAP8AAAD/AAAA/wAAAP8AAAD/AAAA/wsUF/913P//a8z//2jM//9ly///Y8r//2LK//9gyv//YMr//3XQ//9qzP//P7r3/AAAAABEwf7/hdX//6be//+V2///k9r//5HZ//+P2P//i9f//4rW//+M3P//Ypq6/wICAv+E1f//QGqA/3jJ9P89aoD/arnh/0d+mv9Wmbz/DRgd/3re//9szP//a8z//2nM//9ly///Y8r//2HK//9hyv//fND//3DM//8/uvf8AAAAAEXB/v+G1v//qN///5fc//+V2///k9r//5HZ//+P2P//i9f//47d//9dnLr/AAAA/4ba//8/YXX/fc74/z9rgv9tu+P/Q3eQ/1WZuv8NFx3/euD//2/N//9szP//a8z//2nM//9ly///Y8r//2PK//940f//a83//z+69/wAAAAAR8H+/4zW//+r4P//mNz//5fb//+V2///k9r//5HZ//+P2P//kN7//2Seu/8AAAD/HzE6/wQHCP8dLjb/BQgK/xcmLf8KERX/ER0j/xEdJP9+4f//cM7//27N//9szP//asz//2nL//9ly///ZMv//3/R//9szf//P7v3/AAAAABFwf3+h9X//6vg//+Y3P//mNz//5fc//+V2///k9r//5HZ//+V3///YJy6/wIDA/+S5///SHKJ/4nd//9Gcon/eMbv/1GHpv9gpcj/DRgc/3/i//9zz///cM7//2/N//9szP//a8z//2nL//9ny///e9L//3LN//9Au/f8AAAAAEbB/P6H1v//rOH//5vd//+Y3P//mNz//5fc//+U2///k9r//5bg//9qnbr/AAAA/3m94P8uSFb/b7HT/zBNXv9hnrz/PGV6/0x/mf8PGR7/geP//3XQ//9zz///cM7//2/N//9szP//asz//2rM//+C0v//bc3//0C79/wAAAAASsL8/ojW//+v4f//nd3//5vc//+Y3P//mNz//5fc//+V2///mOL//2qfuv8AAAD/NlBe/xQfJP8vSVb/FiAm/ypEUf8aKTH/IzhE/xEdI/+F5P//d9H//3XQ//9zz///cM7//2/N//9szP//a8z//37T//90zv//Qrv3/AAAAABJwvz+idf//6/h//+e3v//nd3//5rc//+Y3P//mNz//5fc//+a4///a566/wIEA/+f8f//S3SJ/5Hh//9JdIv/f8zz/1iMqf9qqs7/Dhcc/4fm//960v//d9H//3XQ//9zz///cM7//2/N//9tzf//htT//2/O//9Du/f8AAAAAEnC+/6I1v//sOL//6He//+e3v//nd3//5rc//+Y3P//mNz//53l//9soLr/AAAA/1yJof8dKzL/VYGZ/x8xOf9IcYb/LEJQ/zNXaf8SHCD/i+X//3zT//960v//eNL//3XQ//9zz///cM7//3DO//+H1P//cM7//0O79/wAAAAASsH6/ofW//+x4v//o9///6He//+e3v//nd7//5rc//+Y3P//nuT//2ydtv8IDA7/CQ0O/xAYHP8LDxP/CxAU/w8SFv8OExf/BwsN/x4vO/+L4v//gNP//3zT//960v//d9L//3XQ//9zz///cc7//4PU//9wzv//Q7v3/AAAAABMwfr+iNb//7Lj//+k4P//o9///6He//+e3v//nd7//5rc//+e5P//ZpSs/wAAAP9Ianz/AAAA/xQfJP81T1z/AAAA/woKC/9Ea4D/CAoL/4jc//+C1P//f9P//3zT//950v//d9L//3XQ//900P//itX//3DO//9DvPf8AAAAAEzA+f2I1v//s+P//6Xg//+k4P//o9///6He//+e3v//nd7//5vc//+m7///NU1Y/2ydtf8AAAD/MEdT/1+Opv8JCQn/BgoL/2WduP9jnLv/it7//4PU//+C1P//gNP//3zT//960v//d9H//3fR//+M1v//cM7//0S69voAAAAAU73z4nnR//+75f//quH//6Xg//+k4P//o9///6De//+e3v//nd3//5/i//99tND/LEFK/wAAAP8AAAD/AAAA/wAAAP8mOkP/KkBL/5Tm//+H1f//hdT//4PU//+C1P//f9P//3zT//970v//gdP//5TY//9kyv//Rbny2wAAAABWu+iiTsb+/8js//+55v//q+L//6Xg//+k4P//o9///6He//+e3v//nd3//5vh//+l8P//baS+/2KOpP96tNL/da7L/5Xg//+X5v//i9f//4nW//+H1f//hdX//4PU//+C1P//gdP//4bV//+Y2///quH//0DB/v9JteuZAAAAAGaqxTJKwPr6gNP//930///F6v//t+b//7Dj//+s4///rOL//6rh//+o4f//p+H//6bg//+k5P//oub//6Hl//+f3v//nd3//5zd//+a3P//mNv//5Xa//+T2f//ktn//5PZ//+b3P//reP//8fs//9vzv//P7v5+VygxS8AAAAAAAAAAFi33YFEwv3+hdX//+j4///s+f//5ff//+Ty///k8v//4/f//+Tx///i9v//4fD//+Dw///h8P//3/X//+D1///f9f//3PT//9v0///a8///2/P//9r0///Z8v//2vP//+H2///c8///eNH//zq9/P5Lsd99AAAAAAAAAAAAAAAArVIfAliz34FIwPr6T8b+/4TU//+Z3P//nN3//5ze//+c3v//m93//5rd//+Z3P//mdz//5nc//+Z3P//mdz//5nc//+Y3P//mNz//5fb//+W2///ltv//5Xb//+R2f//etH//0LD/v89vfr5UbTbfgD//wEAAAAAAAAAAAAAAAAAAAAAAAAAAGOlwjVWuuucT73z30q+9vtJwPj9ScD4/UnB+P1Jwfj9R8D4/Ua/+P1Gv/j9R7/4/US/+P1Ev/j9RL/4/UW/+P1Dv/j9Q7/4/US++P1Cvvj9Q774/UG99/pEuvPdS7frmVqevTEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA=="
  },
  EPC: {
    type: "Episode Collection",
    id: 188,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wASAAADEwAACRYAAA0XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFgAADRMAAAgSAAAC////AP///wD///8AEQAAARMAAA8VAAApLgoTQkoUJlRKFCZUShQmVEoUJlRKFCZUShQmVEoUJlRLFCdUSxQnVEsUJ1RLFCdUSxQnVEsUJ1RLFCdUSxQnVEoUJlRKFCZUShQmVEoUJlRKFCZUShQmVEkTJVMnBw0+FAAAJhMAAA0RAAAB////AP///wAUAAADQhIiKI4uWL2hNmb8ojZn/6I2Z/+kN2j/pzhq/6g4a/+qOWz/qjls/6o5bP+rOWz/qzls/6s5bP+rOWz/qzls/6s5bP+qOWz/qjls/6o5bP+oOGv/pTdp/6Q3aP+iNmf/ojZn/6A1ZvmKLVWsLgoTHBQAAAL///8A////ABQAAAOcNGO2ojZn/6I2Z/+lN2n/qjls/646bv+zPHL/tj10/7c9dP+3PXT/uT51/7k+df+5PnX/uT51/7k+df+5PnX/uT51/7k+df+3PXT/tz10/7Y9dP+zPHL/rjpu/6o5bP+kN2j/ojZn/6I2Z/+aM2GXFAAAAv///wD///8AnTRkIaI2Z/6iNmf/pzhq/646bv+2PXT/uj52/79Aef/AQnv/wUR8/8FEfP/BRHz/wUR8/8FEfP/BRHz/wUR8/8FEfP/BRHz/wUR8/8FEfP/BRHz/wEJ7/79Aef+6Pnb/tDxy/606bv+lN2n/ojZn/6I2Z/aiNmcI////AP///wCiNmc+ojZn/6U3af+vPXD/tz10/79Aef/BRHz/wkh//8NLgf/EToP/xE6D/8ROg//EToP/xE6D/8ROg//EToP/xE6D/8ROg//EToP/xE6D/8ROg//DS4H/wkh//8FEfP+9P3j/tj10/606bv+kN2j/ojZn/6I2Zx7///8A////AKI2Zz+iNmf/qzls/7hGev+/QHn/wkd+/8RNg//FUYX/xlSH/8dWif/HV4r/x1eK/8dXiv/HV4r/x1eK/8dXiv/HV4r/x1eK/8dXiv/HV4r/x1aJ/8ZUh//FUIX/w0uB/8FFff+9P3j/tDxy/6o5bP+iNmf/ojZnH////wD///8AojZnP6U3af+wO3D/vkyA/8JKgP/GVIj/x1iK/8lej//KYJD/ymOS/8tkkv/LZJL/y2WT/8tjkv/LZpT/yl+P/8pfj//KX4//yl+P/8pfj//JXY7/yFqM/8dXiv/GU4f/w0uB/8FEfP+6Pnb/rjpu/6Q3aP+iNmcf////AObm5gitVHxIqT1u/7ZFeP/Xqb7/27rJ/97E0P/ZrcH/4M/X/9uyxP/gzdb/3LrK/929zP/fx9L/27TG/+LW3P/LY5L/y2OS/8tjkv/LY5L/y2OS/8tikf/KYJD/yVyN/8dXiv/FUIX/wkh//79Aef+zPHL/pTdp/6I2Zx////8A5ubmAKI2Zz+qOWz/tz10/9u7yf/fz9b/4NLZ/9y6yf/i3N//3cDN/+La3f/fx9L/38rT/+HU2v/dwc7/5OTk/8xmlP/MZpT/zGaU/8xmlP/MZpT/zGaU/8tjkv/KYJD/yFqM/8ZUh//DS4H/wEJ7/7Y9dP+oOGv/ojZnH////wDm5uYApDdoP6s5bP+5PnX/ym2X/858of/g09n/27jI/+HZ3f/cvcv/4dbb/97F0P/ex9H/4NTZ/9qvwv/WmrX/zWmW/81plv/NaZb/zWmW/81plv/NaJb/zGaU/8tikf/JXY7/x1aJ/8ROg//BRHz/tz10/6o5bP+kN2gf////AObm5gClN2k/rTpu/7xAev/JTo3/zlyY/+Xd4f/hxtP/5uDj/+PL1v/m3uH/48/Y/+LP2P/j2t3/2am//85rmP/Oa5j/zmuY/85rmP/Oa5j/zmuY/81plv/MZpT/y2OS/8pfj//HV4r/xE6D/8FEfP+3PXT/qjls/6U3aR////8A5ubmAKU3aT+tOm7/v0J+/85VmP/SZqL/5t3h/+PJ1f/o4uX/5s/Z/+ni5f/o19//6Nng/+ri5f/mxtX/3Yy4/9iArf/Rcp//zmuY/85rmP/Oa5j/zWmW/8xmlP/LY5L/yl+P/8dXiv/EToP/wUR8/7k+df+qOWz/pTdpH////wDm5uYApTdpP606bv/AQ4D/0Feb/9Njo//YirP/3aS+/+no6P/m0Nr/6ePl/+jZ4P/o2eD/4qzG/+KkxP/ilsL/45jD/+Oaxf/fkLz/1Xun/85rmP/NaZb/zGaU/8tjkv/KX4//x1eK/8ROg//BRHz/uT51/6s5bP+lN2kf////AOXl5QClN2k/rTpu/8FEgv/SWZ7/1Wam/9dwq//clrr/6urq/+bT3P/q5Of/6dvi/+nd4v/ilsH/4pfD/+OZxP/km8b/5Z3I/+afyv/moMv/4pfD/9N3pP/MZpT/y2OS/8pfj//HV4r/xE6D/8FEfP+5PnX/qzls/6U3aR////8A4+PjAKU3aT+tOm7/wkWD/9Nbov/WaKn/2XKv/9yGtv/hscf/5MHR/+rk5//kuMz/5bfM/+OZxP/kmsb/5JzH/+any//npsz/56vO/+ioz//prtL/6anR/96Quv/Na5j/y2OS/8hejv/FU4b/w0yB/7k+df+rOWz/pTdpH////wD///8ApTdpP606bv/DRob/1V2l/9hqrf/adbL/3YG3/9+Iu//hkb//4ZTB/+OYxP/kmsX/5JzH/+Weyf/mn8r/8ejs/+/d5f/y6u3/793m//Lr7v/x5ev/8ubr//Dk6f/et8j/4c3W/9mqv//gztb/vUx//61Acf+3aYwq5eXlCP///wClN2k/rTpu/8VHiP/XX6j/2Wyw/9x3tv/fhLr/4Iu+/+KUwv/jl8T/5JvG/+WdyP/mn8r/56HM/+eizf/z8vP/8ebr//Tx8v/y5Or/9PLz//Ts7//07fD/9fDz//Hk6v/o3+P/3b3M/+fn5/+7R3v/qzls/6U3aR/l5eUA////AKU3aT+tOm7/xkmL/9hhrP/bb7T/3Xq5/+CGvv/hjsH/45bF/+Sax//mn8r/5qDL/+eizf/opM//6aXQ/+3Q3f/u1OD/9fP0//Lm6//28vT/9e3x//Xu8f/28fP/9erv//Xz9P/WlrL/0IOm/7pBd/+rOWz/pTdpH+Xl5QD///8ApTdpP606bv/HSo3/2mOw/91xt//ffLz/4YnB/+OQxP/lmsj/5p3K/+eizf/oo87/6aXQ/+mn0f/qqNP/66rV/+7N3P/29vb/8+ft//bz9f/17vL/9u/y//fy9P/27PD/+fj4/+iu0f/BRHz/uT51/6o5bP+lN2kf5eXlAP///wClN2k/rTpu/8lMkP/bYrL/3nO7/+F/wP/jjMT/5JTH/+ady//noM3/6KTP/+mm0f/qqNP/66rU/+ur1v/srdf/79Hf//f19v/16e7/9/T2//bw8//38fP/+PP1//bt8f/5+Pj/88rn/9RZov+3PXT/qjls/6U3aR/l5eUA////AKQ3aD+rOWz/y06S/91ktf/gc73/4oHD/+WPx//mlsr/55zN/+ij0P/ppNH/6qbT/+uo1f/sqdb/7KvY/+2t2v/utdz/8Nbi//Pi6v/49/j/9/H0//jy9P/59vf/9urv//PG6P/yluX/7XXV/7k+d/+qOWz/pDdoH+bm5gD///8AojZnP6o5bP/LTpT/32W4/+Fzwf/jf8X/5o3J/+eUzf/pntD/6aHS/+um1P/rp9b/7KnX/+2q2f/urNv/767c/++v3v/wsd//9OPr//r5+f/48/X/+PP2//r4+f/36/D/85bm//OH5v/zd97/zE+X/6g4a/+kN2gf5ubmAP///wCiNmc/pzhq/8tOlf/gYrj/43HD/+WAyP/ni8z/6JLP/+mY0f/qn9T/66DW/+yi1//to9n/7qXb/+6n3P/vqN7/8Knf//Gq4f/yx+X/9OLq//jw9P/58vX/9eTs//XE6v/0kuj/9IPn//R13f/ZWqz/pzhq/6I2Zx/q6uoA////AKI2Zz+lN2n/y06V/+Bht//ja8L/5nnK/+eDzf/pjtH/6pXT/+ub1v/snNf/7Z7Z/+6f2//vodz/76Le//Cj3//xpeH/8abi//Kn5P/zqOX/86bm//Sl5//0nej/9Jfp//WM6f/1feT/9HLZ/9lZqf+kN2j/ojZnH////wD///8AojZnP6I2Z//KTpT/4GC2/+Rlv//ncsr/6HzP/+qH0v/ritT/7JDX/+2S2f/tk9r/7pTc/++V3v/wlt//8Zfh//GZ4v/ymuT/85vl//Oc5//0nej/9Jjo//WU6f/1jer/9YPo//V24P/1cdj/3Fqr/6I2Z/+iNmcf////AP///wCiNmc/ojZn/8dLkP/eXbD/42K7/+doxP/pcc3/6nrU/+yB1v/shNj/7Yja/+6J3P/vit7/8Ivf//GM4f/xjeL/8o7k//OP5f/zkOf/9JHo//SO6f/1jer/9YTq//Z+5f/2d+D/9XLY//Vszv/XVqT/ojZn/6I2Zx////8A////AKI2ZyeiNmf/tUF8/95brP/hX7T/5mXA/+lpxv/rbc3/7HPS/+121v/ud9f/73va//B83P/wfd7/8X7f//J/4f/zgOL/84Dk//SB5f/0fuT/9X/l//V64//2d+D/9nPc//Zy2f/1bc7/9GnH/75Ghv+iNmf6ojZnDP///wD///8A////AKI2Z8GiNmf/t0J+/85Qmf/VVqP/2Vmq/9tcrv/dXrL/32C1/+Bgt//hYbn/4mG6/+Jiu//jY7z/42O9/+Rkvv/kZL//5WXA/+VlwP/lZb//5WS//+VjvP/jYbn/4l6z/9xYqf+/R4f/ojZn/6I2Z6L///8A////AP///wD///8AojZnGaI2Z8GiNmf/ojZn/6I2Z/+lN2n/pzhq/6o5bP+rOWz/rTpu/606bv+tOm7/rTpu/606bv+tOm7/rTpu/606bv+tOm7/rTpu/6s5bP+qOWz/pzhq/6U3af+iNmf/ojZn/6I2Z/6iNmeuojZnDf///wD///8A////AP///wD///8A////AKI2ZyeiNmc/ojZnP6I2Zz+iNmc/pDdoP6Q3aD+lN2k/pTdpP6U3aT+lN2k/pTdpP6U3aT+lN2k/pTdpP6U3aT+lN2k/pDdoP6Q3aD+iNmc/ojZnP6I2Zz+iNmc+ojZnIP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  FS: {
    type: "Flow Survey",
    id: 26,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AERAQAg4NDQIODQ0CDg0NAg4NDQIODQ0CDg0NAg4NDQIODQ0CDg0NAg4NDQIODQ0CDg0NAgwLCwIJCQgCCQgIAv///wD///8A////AP///wD///8A////AP///wAAAAABAAAAAQAAAAEAAAABAAAAAQ8ODQExLi0BSUZFARkYFxQAAAAkAAAAJAAAACQAAAAkAAAAJAAAACQAAAAkAAAAJAAAACQAAAAkAAAAJAAAACQAAAAkAAAAIwAAACMAAAAgDw4NAv///wD///8A////AP///wARKjwBBxIbBwEEBgwBAwQOAAAADwAAAA8AAAAPAAAADwwMCxV/eHXrgXp3/4F6d/+Benf/gXp3/4F6d/+Benf/gXp3/4F6d/+Benf/gXp3/4F6d/+Benf/gXp3/4F6d/+Benf/fHZz7QAAACMREA8C////AP///wD///8A////ABkzRg0MHSpEDB0rUgwdK1QMHStUDB0rVAwdK1QMHStUHi05XoiBf/////////////////////////////////////////////////////////////////////////////////+Benf/AAAAIxUUFAL///8A////AP///wBNiLAlO4G13zR7sv8yebD/Mnmw/zJ5sP8yebD/Mnmw/zF4r/82d6v/iIF////////68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7//////4F6d/8AAAAjGhgYAv///wD///8A////AEyVx8Bvq9L/0fD6/9X0/f/U9P3/1PP9/9Tz/f/T8/3/0PD6/73Z4v+IgX////////rz7//68+//+vPv//rz7//68+//+vPv//rz7//68+//+vPv//rz7//68+//+vPv//rz7///////gXp3/wAAACMaGBgC////AP///wBVns8CT5vP+7nf8f+w7P//nuf//5zm//+a5f//luP//5Lh//+N3Pz/fsPh/4iBf///////+vPw//rz8P/Nsqb/zbKm/82ypv/Nsqb/zbKm/82ypv/Nsqb/zbKm/82ypv/68/D/+vPw//7+/v+Benf/AAAAIxoYGAL///8A////AFWg0QVRntH/vuT0/6nq//+U5f//k+T//5Hj//+O4f//it///4Ta/P92weH/iYN////////69PD/+vTw//r08P/69PD/+vTw//r08P/69PD/+vTw//r08P/69PD/+vTw//r08P/58/D//Pz8/4F6d/8AAAAjGhgYAv///wD///8AV6LTBVKf0v+/5PT/qer//5Xl//+U5f//k+T//5Hj//+O4f//iNz8/3rE4f+LhYH///////r08f/69PH/zbOm/82zpv/Ns6b/zbOm/82zpv/Ns6b/zbOm/82zpv/Ns6b/+vTx//fx7//4+Pj/gXp3/wAAACMaGBgC////AP///wBXotMFUp/S/7/k9P+p6f//leT//5Xl//+U5f//k+T//5Hj//+M3/z/f8fi/46HhP//////+/Xy//v18v/79fL/+/Xy//v18v/79fL/+/Xy//v18v/79fL/+/Xy//r08v/48vD/9O/t//T09P+Benf/AAAAIxoYGAL///8A////AFii0wVSn9L/vuT0/6np//+V5P//leT//5Xl//+U5f//k+T//4/g/P+CyeL/kYqG///////79vP/+/bz/860p//OtKf/zrSn/860p//OtKf/zrSn/860p//OtKf/zbSo//Tw7v/w7Or/7+/v/4F6d/8AAAAjGhgYAv///wD///8AWKLTBVKf0v++5PT/qOj//5Tj//+V5P//leT//5Xl//+U5f//kuH8/4XK4v+UjYn///////v29P/79vT/+/b0//v29P/79vT/+/b0//v29P/79vT/+vbz//jz8f/08O//8Ozr/+zo5//p6en/gXp3/wAAACMaGBgC////AP///wBYotMFUp/S/77k9P+n5///k+L//5Tj//+V5P//leT//5Xl//+T4vz/h8zi/5eQjP//////+/f1//v39f/Otaj/zrWo/861qP/Otaj/zrWo/861qP/Ntan/zLaq/8u2rP/r6Of/5uTj/+Tk5P+Benf/AAAAIxoYGAL///8A////AFii0wVSn9L/vuT0/6bn//+S4f//k+L//5Tj//+V5P//leT//5Pi/P+IzOL/m5OP///////7+Pb/+/j2//v49v/7+Pb/+/j2//v49v/69/X/+PXz//Ty8P/w7uz/6+no/+bk4//h4N//3t7e/4F6d/8AAAAjGhkYAv///wD///8AWKLTBVKf0v++5PT/peb//5Hg//+S4f//k+L//5Tj//+V5P//k+L8/4jM4/+elpL///////v49//7+Pf/zrWq/861qv/Otar/zbWq//j19P/08vH/8O7t/+zq6f/m5eT/4d/f/9zb2v/Z2dn/gHl2/wAAACMcGxoC////AP///wBYotMFUp/S/77k9P+k5P//j97//5Hg//+S4f//k+L//5Tj//+T4fz/iMzj/6GZlf//////+/n4//v5+P/7+fj/+/n4//r49//49vX/9PLy//Du7v/s6un/5eTj/93c2//X1tX/0tHR/9HR0f+AeXb/BQUFGv///wD///8A////AFii0wVSn9L/vuT0/6Pj//+O3f//j97//5Hg//+S4f//k+L//5Pg/P+JzOP/pJyY///////8+vn//Pr5/862q//Otqv/zbar/8y3rf/x7+//7Ovq/+fm5f+3sK3/rKaj/6Gcmf+XkpD/i4aE/4B5du9PTEoC////AP///wD///8AWKLTBVKf0v++5PT/ouL//4zb//+O3f//j97//5Hg//+S4f//kt/8/4nL4/+nn5v///////z6+f/8+vn/+/n5//n39//19PP/8fDv/+zr6v/n5ub/4uDg/7y1sv/29vb/9PT0/8fFxP+DfXrzaWZlPv///wD///8A////AP///wBYotMFUp/S/77k9P+g4v//i9r//4zb//+O3f//j97//5Hg//+Q3vz/iMvj/6qhnf///////Pv6//v6+f/49/f/9fT0//Hw8P/s6+v/5+bm/+Lh4f/d3Nz/wLm2//f39v/Kycj/gn9//yssLU08QEME////AP///wD///8A////AFii0wVSn9L/vuT0/6Dg//+J2f//i9r//4zb//+O3f//j97//4/d/P+HyuP/q6Of///////7+vr/+fj4//X09P/x8PD/7Ozs/+fm5v/i4eH/3d3d/9jX1//DvLj/ysjH/4J/f/9EeaL/BQ0TGiIsNAT///8A////AP///wD///8AWKLTBVKf0v++5PT/n+D//4jY//+J2f//i9r//4zb//+O3f//jtv8/4bJ4/+so6D//v7+//z8/P/4+Pj/9PT0/+/v7//p6en/5OTk/97e3v/Z2dn/1NTU/7mzr/+Lh4X/ob3M/zJ5sP8FDRMaEB8rBP///wD///8A////AP///wBYotMFUp/S/77k9P+e3///h9f//4jY//+J2f//i9r//4zb//+M2vz/g8nl/6Shn/+nnpr/pp2Z/6Sbl/+imZX/n5aS/5uTj/+YkIz/lYyI/5GJhf+NhoL/ioiG/53O4P+32+3/Mnmw/wUNExoMHiwE////AP///wD///8A////AFii0wVSn9L/vuT0/57f//+G1v//h9f//4jY//+J2f//i9r//4vZ/P+Cy+r/gsro/4TL6P+Fzej/hs7o/4fP6P+Hz+j/h9Do/4fQ6P+H0Oj/htDo/4rY8v+N4P7/oub//7fb7f8yebD/BQ0TGgweLAT///8A////AP///wD///8AWKLTBVKf0v++5PT/nt///4bW//+G1v//h9f//4jX/v+G1fr/hdH0/4TP8P+F0PD/h9Hw/4nT8P+K1PD/i9Xw/4zW8P+N2PH/kN33/5Lh+/+T4vz/k+T+/5Hj//+k6P//t9vt/zJ5sP8FDRMaDB8uBP///wD///8A////AP///wBXotMFUp/S/77k9P+e3///htb//4bW//+G1v//hdT7/3vC5v9vr87/bqzK/2+tyv9wrsr/crDK/3Oxyv90ssr/dbPK/3i4z/+Hzuf/k+L8/5Xl//+U5f//k+T//6fp//+32+3/Mnmw/wUNFBkRKj4D////AP///wD///8A////AFei0wVSn9L/vuT0/57f//+G1v//htb//4bW//+E0vr/l6Ss/52YmP+alZX/lpKS/5OPj/+QjIz/jomJ/4uHh/+Khob/ioaG/4maoP+S4fv/leT//5Xl//+U5f//qOr//7fb7f8yebD/CholFBc5VAL///8A////AP///wD///8AWqTUAVKf0va13fH/r+b//57f//+e3///nt///53d/P+jnp7/5ubm/9jY2P/W1tb/1tbW/9bW1v/W1tb/1tbW/9fX1//i4eH/ioiJ/6jo/f+p6f//qer//6nq//+47v//rNTo/zR7sfQkR2AH////AP///wD///8A////AP///wD///8AWaPUpGmt2f+54PL/vuT0/77k9P++5PT/vuT0/56wvP+mo6T/3Nvb/+Dg4P/g4OD/4ODg/+Dg4P/g4OD/4eHh/5eUlf+TprL/v+T0/7/k9P+/5PT/v+T0/7fd8P9ZnMn/Q4e4o0F6owH///8A////AP///wD///8A////AP///wBmq9gNWKPUqlKf0vhSn9L/Up/S/1Kf0v9Sn9L/UZ7R/4Sesf/Z19f/+fn5//n5+f/5+fn/+fn5//n5+f/j4uL/gI6Z/1Ge0f9Sn9L/Up/S/1Kf0v9RntH/T5vP+FCYy6ddnMcL////AP///wD///8A////AP///wD///8A////AP///wD///8AYKfWA1+n1QZhqNYGYajWBmKm0gZwpMcGlqSwY6Sfn/uinp3/oJub/52ZmP+alpX/l5OS/5SPj/2NlZuIc6LBBmOiywZgp9UGYajWBl6m1QZdpNID////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  IFN: {
    type: "Ground Infiltration",
    id: 14,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AvVcvvMFhNP/QgUX/z35G/9CAR//RgEn/0YFK/9KAS//RgEz/0H9M/858Sf/LeEf/yHVF/8VxQv/DbkH/wWxA/8BrQP+/aUD/vmhA/71nQP+8ZkD/vGVA/7xlQP+8ZUD/vGVA/7xlQP+8ZUD/vmhB/6I4Mf+YJSvG////AP///wC9Vy+9x246/9qbV/+8XEn/wmJP/8xtWP/XeGH/34Nq/+iNcP/tk3X/8JZ2/+6Vcv/oj2n/4IVd/9d8Uf/Qc0f/zG9C/8xuQv/MbkL/zG5C/8xuQv/MbkL/zG5C/8xuQv/MbkL/zG5C/81xQ//kp1b/sFA5/5glK8b///8A////AL1XL73Hbjr/2p5X/75mSP++ZEj/wmpN/8pzU//TfFv/24Zj/+OPav/qmHD/7550//KhdP/woHH/65pp/+SSX//dilX/1oNM/9J/R//SfUf/0n1H/9J9R//SfUf/0n1H/9J9R//SfUf/039I/+WpVv+wUDn/mCUrxv///wD///8AvVcvgL1YL9LAXjLSwF4y0sBeMtLAXjLSwF4y0sBeMtLAXjLSwF4z0sBeM9K/XDPSvVoz0rtYMtK5VjLSt1My0rVQMdKyTTHSsEow0q5GL9KrQy/SqkAv0qc9L9KlOi7Sozgu0qI2LtKgNC7SnzIu0pkoK9KYJSuG////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AfSUiD54wK3qfLyyWjionGf///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AHomIRWhMSuBqkIy8K9LNvafLyyejCkmIf///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wB9KSESojMrgq1HM+vSiE7/2ZNS/7FQN/OfLyydjSknHf///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AfSohBqQ2K4OuSDPu1IxQ/+ScXP/hlVn/2JJR/7BONvSfLyyjiigmDP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AIAsIgulOSyEsU01+dmQVP/poGL/4Ihd/tyCWP/gk1j/2pZT/7FPN/ufLyyljCkmE////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wCALiEVqDsshLNPNvTdllj/7qZp/+aPZf/jh2D/34Nb/9yCV//hlFj/3JhU/7BNNvifLyygjCkmH////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8Agi8hFak9LIS1Ujbs3ZVY//Kpbv/slG3/6I5o/+WKZP/hh1//3oNb/9yCVv/glFj/2ZNR/7FPN/OfLyycjCkmH////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AIk0IwurQCyFt1Q37N2WWf/yqnD/8Jdy/+2TcP/rkGz/541o/+SJY//hhl7/3oJa/9uBVv/fklf/2JFQ/7FPN/OfLyygjCkmE////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wCLNiQGrUItiLhWNvXfmFr/8qpx//GZdv7vlXX/7pRy/+ySb//qkGz+541n/+SJY//hhl7/3YJZ/9qBVf7fklb/2JNR/69NNvifLyyliigmDP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AjzklFK9FLYi6Wjj54Zxd//Oqc//wmHb/8JZ3//GWdv/wlXT/7pRy/+ySb//qkGv/541n/+SJYv/hhV7/3YFZ/9qAVf/fklb/25dT/7BPNvufLyyjjSknHf///wD///8A////AP///wD///8A////AP///wD///8A////AI45JBexRy6Iu1o379+ZW//xqXH/7pd0/++Vdv/wlXf/8JZ3//CWdv/wlXT/7pRy/+ySbv/qj2r/54xm/+OJYv/ghV3/3YJY/9uCVP/glVf/2ZVR/7BONvSfLyydjCkmIf///wD///8A////AP///wD///8A////AP///wCUPSYSskkui71dN+3enFf/8rls//Gwb//yr3D/861y//GfdP/wlnf/8JZ3//CWdv/vlXT/7pRx/+yRbv/pj2r/5oxl/+WQYv/ooWD/56Re/+akXP/pr1z/2plS/7FQN/OfLyyejionGf///wD///8A////AP///wD///8A////ALNLLnyzSy7yulk1/8RsP//GbUH+xWxB/8VsQf/QgUz/8K5t/vCWdv/wlnf/8Jd3/++Wdf7vlXT/7ZNw/+uRbf/pjmn/6qRk/tGFTf+7Xz3/ul48/7ldPP63Wzv/rEUy/6AxLPafLyuV////AP///wD///8A////AP///wD///8Aq0grSatIK4arRiuGqkUrhqlEK4aqRCyGrkYtrbdSNPHtr2j/75d1/++Vd//wlnf/8JZ3//CWdf/vlXP/7pNw/+ySbf/rqWX/uVw7+qQ2K7qdMyqGmzEphpowKYaZLymGmC4phpctKVj///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wCePylSt1M04+yuaP/tlXT/7pN2/++Vdv/wlnf/8Zd2//CWdf/vlXP/7ZRw/+2qZv+7XTz0oDUqbv///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AJA6JVK4VDTj661n/+uTc//skXT/7pN2/++Vd//wlnf/8ZZ2//CWdf/vlXL/7qto/7tePPScNSlu////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AkDolUrhVNOPqrGX/6ZBx/+uPdP/tknX/7pR2//CVd//wlnf/8ZZ2//CWdP/urGn/vF889J02Km7///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wCRPCVSuVY04umrZf7njW//6I1x/+uQdP/tknX+75R2/++Vd//wlnf/8JZ2/++tav69YDz0nTgpbv///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AJI9JVK6VzPj6Kpk/+SKbf/minD/6I1y/+uQdP/tknX/75R2//CVd//wlnf/765s/71hPfSeOSpu////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8Akj4lUrpYM+PnqGP/4Ydq/+OGbf/minD/6Y1y/+uQdP/tk3X/75R2//CWd//vrmz/vmI99J86Km7///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wCTPiVSu1g04+anYv/fhGj/4YRr/+SHbf/ni3D/6o5z/+yRdP/uk3X/75V2/++ubP+/Yz30oDsqbv///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AJM/JVK7WTTi5aVg/tuAZf/dgGj/4YRr/+SHbf7ni3H/6Y5y/+yRdP/ulHX/7q1r/r9kPfShPClu////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AlEAmUrxaNOPkpF//2X1j/9t9Zf/egWj/4YVr/+WJbv/njHH/6o9y/+ySdP/urGv/wGU99KI9Km7///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wCVQSZSvFs04+SnX//fk2P/4ZRl/+SXZ//mmmn/6Z1s/+ugbv/to2//76Vx/++xav/BZT30oz4qbv///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AJVBJlK6VjHiz35G/9CBSv/RgUr/0YJL/9GCS//Sgkz/0oNM/9ODTf/Tg03/0IBL/7hWNfSjQCpu////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AlUImLrhRL6C5VDDAuVMxwLhSMMC4UjDAt1EwwLZQMMC1TzDAtE4wwLRNMMCzSzDAsEcuraRAK0L///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  INFR: {
    type: "Inference",
    id: 158,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wCSjo40ko2NkpGNjZKQjIySkIuLko+Li5KPioqSjoqKko6JiZKNiYmSjYiIkoyIiJKMh4eSi4eHkouGhpKKhoaSioWFkomFhZKJhYWSiISEkoiEhJKIhISSh4ODkoeDg5KHg4OSh4ODkoeDg5KHg4NG////AP///wD///8A////AJOOjn+xrq7/z83N/8/Nzf/Ozcz/zszM/87MzP/OzMz/zszM/83MzP/Ny8v/zcvL/83Ly//My8v/zMrK/8zKyv/Mysr/zMrK/8zKyv/Lysr/y8nJ/8vJyf/Lycn/y8nJ/8rJyf/Kycn/sa6u/4eDg5////8A////AP///wD///8Ak4+Pf8jGxv/8+/v/+/j3//v49//7+Pf/+/j3//v39v/79/b/+/f2//r39v/69/X/+vb1//r29f/69vX/+vb1//r29P/69vT/+vb0//r29P/69vT/+vb0//r29P/69vT/+vb0//v6+f/Qz8//h4ODn////wD///8A////AP///wCUkI9/yMbG//z6+f/16eT/9Obi//Pl4P/y5N//8uPd//Li2//x4dr/8N/Y//De1//v3NX/79vU/+7a0//u2dL/7tjR/+3Y0P/t19D/7dfP/+3Xz//t18//7dfP/+3Xz//t2ND/+fTz/9DPz/+Hg4Of////AP///wD///8A////AJWQkH/Jxsb//Pr6//bq5v/16OP/9Ofi//Tl4f/z5N//8uPd//Hi2//x4dr/8N/Y//De1v/v3NX/79vU/+7Z0v/u2NH/7djQ/+3Xz//t1s//7dbO/+3Wzv/t1s7/7dbO/+3Wzv/59PP/0c/P/4eDg5////8A////AP///wD///8AlZGRf8nHx//8+/r/9+zp//bq5v/16eX/9ejj//Xn4v/05eH/8+Tf//Lj3f/u39j/7NzV/+zc1f/u3NX/79zV/+/a1P/u2dL/7tnR/+3Y0P/t18//7dbO/+3Wzv/t1s7/7dbO//n08//Rz8//h4ODn////wD///8A////AP///wCWkpF/ycfH//z7+v/47uv/9+zo//br5//26ub/9unl//Xo4//05uH/yr65/4h4Zv+Ec17/hHNe/6WWi//q2dL/8N3W/+/c1f/v29T/7tnS/+7Y0f/t19D/7dbP/+3Wzv/t1s7/+fTz/9HPz/+Ig4Of////AP///wD///8A////AJeSkn/Kx8f//Pv7//jv7P/47ur/9+3p//fs6P/26+f/9urm/+/j3/97aU//dlAJ/3pSCf96Ugn/bkwN/9fJwv/x4Nn/8N/X//Dd1v/v3NX/79rT/+7Z0v/u2NH/7dfP/+3Xz//59PP/0c/P/4iEhJ////8A////AP///wD///8Al5OSf8rIyP/8+/v/+fDt//jv7P/47uv/9+3q//ft6f/37Oj/7ePf/3ZjR/90Twn/dlAJ/3ZQCf9vSwj/0cS+//Hi2//x4Nr/8N/Y//De1//v3NX/79rU/+7Z0v/u2NH/7tjR//n18//R0ND/iISEn////wD///8A////AP///wCYk5N/ysjI//z7+//58O3/+fDt//nv7P/47+z/+O7r//ft6v/x5+T/fm5V/3ZQCf97VAr/elIJ/21MEf/czsn/8uTf//Lj3f/x4tv/8eDa//Df2P/w3db/79vV/+/a0//u2tP/+vXz/9HQ0P+JhYWf////AP///wD///8A////AJiUlH/LyMj//Pv7//nw7f/58O3/+fDt//nw7f/57+z/+O/s//ft6v/Wzcr/lYp9/5CEdv+QhHf/tKmi/+/j3v/05+L/8+Xg//Pk3//y493/8eHb//Hg2f/w3tf/793W/+/c1f/69fT/0dDQ/4mFhZ////8A////AP///wD///8AmZWUf8vJyP/8+/v/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+e/s/+bd2v++tbH/ubGt/7qxrP/TyMT/8+fj//Xp5f/16OP/9Ofi//Pl4P/y5N//8uLc//Hh2v/w39j/8N/Y//r29P/S0ND/ioaFn////wD///8A////AP///wCalZV/y8nJ//z7+//58O3/+fDt//nw7f/58O3/+fDt//nw7f/17On/iHll/3RPCf94UQn/eFEJ/3BSHP/h19P/9uvn//bq5v/26eX/9ejj//Tm4f/z5eD/8uPe//Hi2//x4dr/+vb1/9LQ0P+Khoaf////AP///wD///8A////AJqWlX/Lycn//Pv7//nw7f/58O3/+fDt//nw7f/58O3/+fDt//Xs6f+Ie2n/dlAJ/3pSCf99VQr/dlAJ/6aclP/z6OX/9+vo//br5//26eX/9ejk//Xn4v/z5eD/8uTe//Lj3f/69/X/0tDQ/4uGhp////8A////AP///wD///8Am5aWf8zJyf/8+/v/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt/8G5tf9wTg3/dlAJ/3pSCf96Ugn/clQe/8G4tP/z6eb/9+3p//fr6P/26ub/9unl//Xo4//05uH/8+Xg//r39v/S0dH/i4eHn////wD///8A////AP///wCbl5d/zMrK//z7+//58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/8enm/5KHef9zTgr/eFEJ/3hRCf96Ugn/dFUd/7evqv/06uf/9+3q//fs6f/26+f/9urm//Xo5P/15+P/+/j3/9LR0f+Mh4ef////AP///wD///8A////AJyXl3/Mysr//Pv7//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/7eTh/42Ccv9zTgv/dlAJ/3hRCf97VAr/dFQZ/8O6tv/27en/+O7q//ft6f/37Oj/9urm//bp5f/7+Pf/09HR/4yIiJ////8A////AP///wD///8AnJiYf83Kyv/8+/v/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/7uXi/5aMf/9yTw3/eFEJ/3pSCf97VAr/dl40/+je2//47+z/+O7r//ft6v/37Oj/9+vn//v5+P/T0dH/jYiIn////wD///8A////AP///wCdmJh/zcrK//z7+//58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/7ubj/4Z5aP92UAn/elIJ/3tUCv92UAn/sKeg//jv7P/47+z/+O/s//ju6v/37er/+/n4/9PR0f+NiYmf////AP///wD///8A////AJ2ZmX/Ny8v//Pv7//nw7f/58O3/+fDt//nw7f/47+z/9+7r//nw7f/58O3/+fDt//nw7f/58O3/z8fE/3RQDf97VAr/fVUK/3hRCf+NgG//9u3q//nw7f/58Oz/+O/s//jv6//7+vn/09LS/46Kip////8A////AP///wD///8AnpmZf83Ly//8+/v/+fDt//nw7f/58O3/+fDt/9DIxP+YjoL/3NTR//Pq5//47+z/+fDt//fu6//Hv7z/dlEM/3tUCv97VAr/eFEJ/4d6Z//17On/+fDt//nw7f/58O3/+fDt//z6+f/T0tL/j4qKn////wD///8A////AP///wCempl/zsvL//z7+//58O3/+fDt//nw7f/47+z/nJKH/3RPCf9yVR//h3pm/66lnv/EvLf/rqWe/3VfOP96Ugn/e1QK/3pSCf90Twn/lot///bt6v/47+z/+O/s//jv7P/47+z/+/n4/9PS0v+Pioqf////AP///wD///8A////AJ+amn/Oy8v//Pv7//nw7f/58O3/+fDt//fu6/+akIX/dE8J/3pSCf96Ugn/eFEJ/3ZQCf96Ugn/elIJ/3pSCf94UQn/eFEJ/29NDv/Kwr7/9u3q//Hp5v/u5uP/7ebj/+7m4//y8O//zs3N/46Kip////8A////AP///wD///8An5uaf87MzP/8+/v/+fDt//nw7f/58O3/+O/s/6GXjf9yTQn/eFEJ/3ZQCf92UAn/dlAJ/3ZQCf94UQn/dlAJ/3pSCf9zTgr/joFx//Ho5f/w6OX/49vY/9rSz//X0M3/2dHP/+Df3v/GxMT/jYiIoP///wD///8A////AP///wCgm5t/zszM//z7+//58O3/+fDt//nw7f/58O3/4dnW/3xsU/9wUBX/dE8J/3hRCf96Ugn/elIJ/3pSCf92UAn/cVQg/5ySh//t5OH/9+7r/+Pc2f+zrq3/rKel/6ulpP+sp6b/sq+u/6ilpf+Pioqg////AP///wD///8A////AKCbm3/OzMz//Pv7//nw7f/58O3/+fDt//nw7f/58O3/8Ojl/9/X1P+7s67/m5GH/42Ccv+NgXD/l42A/7evqf/j29j/9ezp//nw7f/37uv/0MrI/6SgoP/DwMH/wL6//7u4uP+sqKn/ko6N/ZGMjFv///8A////AP///wD///8AoJybf8/MzP/8+/v/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/47+z/9u3q//bt6v/37uv/+fDt//nw7f/58O3/+fDt//fu6//Qysj/sa6u/+fm6P/e3d7/ysjJ/5mVlf2Tjo5m////AP///wD///8A////AP///wChnJx/z8zM//z7+//58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/9+7r/9HKyP+wrK3/3t3e/8rIyf+alpb9lJCQZ////wD///8A////AP///wD///8A////AKKcnH/Pzc3//Pv7//nx7v/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/47+z/083L/6ypqf/KyMn/m5eX/ZWRkWf///8A////AP///wD///8A////AP///wD///8Ao52df9DNzf/8/Pz//Pv7//z7+//8+/v//Pv7//z7+//8+/v//Pv7//z7+//8+/v//Pv7//z7+//8+/v//Pv7//z7+//8+/v//Pv7//z7+v/Z1tb/o5+f/5yYmP2WkpJm////AP///wD///8A////AP///wD///8A////AP///wCjnZ1/ubW1/9DNzf/Pzc3/z8zM/8/MzP/PzMz/zszM/87MzP/OzMz/zsvL/87Ly//Ny8v/zcvL/83Lyv/Nysr/zMrK/8zKyv/Mysn/y8nJ/7q3t/+XkpL9l5KSZv///wD///8A////AP///wD///8A////AP///wD///8A////AKOdnS2jnZ1/o52df6KcnH+hnJx/oZycf6Ccm3+gm5t/oJubf5+bmn+fmpp/npqZf56ZmX+dmZl/nZiYf52YmH+cl5d/nJeXf5uWln+blpZ/mZWVf5eTk03///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  INFINITY: {
    type: "Infinity System Configuration",
    id: 208,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAogk4DKwOOGmrDzavqBA21acQN+WmETXlpQ825aMQNuWhDzXloQ815Z4PNOWdDjXlnA815ZsNMuWaDTPlmQ4x5ZgOMOWWDjDllQ0x5ZMNL+WSDTDlkQ0u5ZEKLtOOCi2qjggsXqoAHgYAAAAAAAAAAAAAAAAAAAAAAAAAALENOEauDTborA42/7UnSf+8Plv/wUdi/8BIYv+/R2H/vkZi/71GYf+8RWD/u0Vg/7tEX/+6RF//uURg/7lFX/+4Q13/t0Re/7dDXf+2Q13/tUNd/7VCXP+0Ql3/rThU/5oeP/+LCSv/iwcq3IoGLD8AAAAAAAAAAAAAAACyDjpMsA02+rgpTf/Zeo3/5YiY/+R+kf/kd4z/4nWL/+N0iv/jc4n/43KI/+Nwh//jcYb/426G/+Nvhf/iboX/422E/+NshP/ja4P/42qD/+Nqgv/iaYH/42mA/+Npgf/jb4X/5n6R/9Ftgf+YID7/iQgq94oGLD8AAAAAuQo6F7MPOvC9MFL/44ub/+JshP/dUHH/20Fl/9o8Yv/aOWD/2Dde/9k1XP/ZM1v/2jFZ/9gvV//YLlX/1yxV/9coU//YKVL/1iVQ/9ckUP/VI0//1iFO/9YgTf/VH0z/1R5M/9clTv/ZNVv/4Fh2/+F8jv+aIT//iwkt4osAHwy3Ez2EtRM7/96Glf/fZ4L/20Jm/9c3Yf/WM1//1jFd/9UvW//YLVn/2StY/9kpVv/XJVT/1yVQ/9YiT//WH03/0hxM/9UcSv/RGkn/1BdH/9MVRv/TFEX/0xNE/9MQQv/PD0H/0g0//9INQP/VHUv/3k9t/9Nug/+MCiz/kAwsbbkUP8/EPF7/44CU/91Mb//bPGT/1zhi/9c3Yf/ZN1//2jJd/9kwW//aLln/2ixY/9oqVv/YJ1T/1yZS/9MkUf/TIU//0h9O/9UeTP/UHEv/1RlJ/9QXSP/UFkf/1BVG/9MSRf/PEUL/zw4//9IOP//XJU//42uE/6AmRv+OCy25uxVA+81Yc//jb4n/3EVq/9xAZv/YPmT/2jti/9w5Yf/cN1//3TJd/90vW//dLVn/3SxY/9wqVv/ZKVT/2ChS/9YmUf/XI0//1x9O/9geTP/XG0v/2BlJ/9YXSP/WFkf/1RVG/9QTRf/PEUL/0g5A/9QWRf/fUXH/s0Fc/5AMLuW9FkD/z1x3/+Jsh//eRWr/3EJo/91AZv/dPmT/3jli/941YP/XLln/yyhS/8gkTv/MJk//1ydU/9wpVv/bJ1T/2yhS/9okUf/ZIE//2BtL/9IYRv/OFEP/zxNC/9QTRP/WFEX/1RRG/9QSRf/SEEL/1BRE/95Hav+2Q1//kg4x8L4WP//QXHf/4m2I/95IbP/eRGr/3kBo/988Zv/bNl7/vyZM/4APLf9QABP/SQAP/10CGf+cFDX/0SJO/94kVP/eI1T/3SJQ/9YbSv+xDjb/gAEh/20AF/9xABn/lQMo/8INOv/WEUP/1RND/9URQ//UE0T/3UZp/7ZDXf+TDjHwwRdB/9Bcef/ibYn/30pu/95Fa//fP2j/1zZf/6UeQP9NABH/Nhce/4iJif+EhIX/dnBx/0YKGv+QCir/0hxK/94dT//TGEf/nQcs/0wAD/9DIiv/Tz1B/003Pf84BBH/eAAZ/8IJN//UD0H/1RFC/9YURP/dRWn/t0Nf/5QOMPDCFkH/0Vt3/+Fvi//fTHD/4ERq/9o7Y/+kH0D/QwQT/4yIif//////////////////////y9fU/1YaKv+PAiT/wA46/4wAIf8yAAH/p6ip/////////////////+r//f9aMTz/gAAZ/8gIOv/VDkH/1hNF/99Gaf+3RF//lg8y8MQXQv/SXHf/43CL/+BKcv/fQWn/xjFW/2UYK/++xsX/////////////////////////////////xcnJ/0QFFP9ZAAT/QwIS/9jk4f///////////////////////////+b9+f9sLD3/rwAq/9UKPv/WE0T/30Zp/7hDYP+XDzLwwxZA/9JaeP/icoz/5miI/+Rhgf+tRmH/t66x////////////////////////////////////////////1tza/zsVH//d4+H//////////////////////////////////////8/V1P+SACT/0Qg6/9cSQ//eRmv/uENg/5cPMfDEF0L/01p2/+Nzjv/oa4z/3WB//6BXaf/7////////////////////65Ko//W5yf//////////////////////8/v4//////////////////7W3//91uD//////////////////v///5AmQP/LBDf/1xBC/95Gaf+5RGD/mBAz8McXQv/TWHX/4nWO/+ZwjP/cYYD/vpGc/////////////////9d1jf/iTXL/4k90/+d7l///+/3///////////////////////3////RVHP/zwAp/9EAKf/SEEH/9+Pp////////////rWl6/8cDNf/WEEH/3UZq/7pDYf+ZDzTwyBZD/9RYdv/jd4//53WQ/91lg//Xtbr////////////4/vv/uEpl/99WeP/hWXz/3VZ4/9CAlf//////////////////////uKaq/55MYf/POl//0wA0/8oAJv+vR2H////////////FkJ7/xwQ0/9YRQ//eSGz/ukRh/5wPM/DJFkT/1Vl3/+J4kf/nepT/4WyJ/+O6xf////////////T9+v9/QVH/p0pi/7RQaf+cR1z/bjdF/+bk5f//////////////////////kHd+/6FbbP/MYnz/qA41/3gsP////////////9CTo//MBjj/1RRE/95Ia/+7RWL/nRA18MsVQv/WWHT/43yT/+h+mP/kdJH/4qOz/////////////////6GXmf9pSFD/ZUBK/3RcYf/IyMf/////////////////////////////////loOH/4RZZf+FYGr/tK6v////////////0W6H/9IJO//WFUb/3Ups/7xEYf+dEDTwzBVE+9ZUdP/jgJf/6YWe/+Z7lv/gfZb///////////////////////j//v/r8vD/////////////////////////////////////////////////zs3P/9TX1v/////////////////MLVX/0w4+/9YaSP/eTG//vUVi/54RNfDNFEP71lV1/+SEmf/qjaP/54Od/+d7lv/wxM/////////////////////////////////////////////ni6L/++Tp////////////////////////////////////////////8c7V/84IOf/UEEH/1xtL/95PcP+9RWL/nxE18M4TQ/vXVXX/4oib/+uTqf/ojKP/6ISd/+iAm//yzdX//////////////////////////////v7/7Zyw/+Z7lv/lf5j/++js///////////////////////////////////////urr7/1ihU/9UTQ//UHUz/3U9x/75FYv+gEDTwzxRF+9dWdf/ii5//7Jqs/+mQpv/pjaP/6Ymh/+mIoP/urb3/+Nzk//709v/87fD/88rV/+uQpv/oh6D/6Img/+iJof/pjqT/88rU///////////////////////75+3/7q+//+ujt//mjqX/0xZE/9UfTP/cT3H/v0Zj/6ERNfDQFEX42FV1/+OOo//unrL/6pes/+qVqv/qkqj/6o+m/+qMo//rjKP/646l/+uOpf/rjqT/65Gn/+uUqv/rlKr/65Wr/+yUqf/skqj/7Zqv//Cywf/ws8L/7aCz/+yZrf/soLP/7Km7//C1xP/cSW3/1R9M/91Pcv/ARWL/pRA18NEVQ/fZVXb/5JKl/+2itv/rnbH/65mt/+uarv/rmK3/65et/+uVq//rlqz/65es/+yarv/smrD/7J6x/+yesv/sn7L/7J2y/+ydsP/tnLD/7Zuv/+2br//tnbH/7aGz/+2muP/trr//8bfG/+qQpv/VHk3/3FBx/8FEYv+mETbw0hZE99lWdv/klKf/76i5/+uhtf/snbH/7J6x/+yfsv/soLP/7J+0/+yesv/soLX/7KG1/+2ktv/tpLf/7aW3/+2mt//tprj/7aW2/+2kt//tpLb/7aa4/+6muP/tqrr/7qq7//Gxwf/yusn/8K++/9UfTf/dTm//wkVg/6cQNvDSFEPw2lFy/+WZq//wrb7/7Ka4/+yhtP/torT/7aO1/+2ktv/tpbf/7aW4/+2muP/tp7n/7ai5/+6ouv/uqbr/7qq7/+6qu//uq7z/7qu8/+6svf/urL3/7q29/++tvf/uscH/8rXE//S8yv/xs8P/1iJQ/9xScv/BP1//qA816NITRMbVNV3/6aa3//G7yP/trbz/7am6/+2mt//tprj/7qi5/+6puv/uqbr/7qq7/+6ru//urLz/7qy9/+6tvf/vrb7/766+/++vv//vr7//76+//++wwP/vsMD/77HA/++1xP/zucf/9L/N//TAzf/XNV//3V9//7crTf+qDza91hNCfdIMPv/jmav/8dHa//LCzf/xscD/8a2+//Gtvv/xr8D/8rC///KxwP/yssL/8rLD//Kzw//ytMP/8rTE//K2xf/ztcX/87fF//O3x//0tsb/9LjG//S4xv/0uMj/9LvJ//W/y//3x9P/9MfS/9lgfv/WZIH/qwgx/64PNnXRBzQS0wo97tYtWP/x3uL/8+nr//Lb4P/0ztj/88vU//PL1f/0ytX/9czW//TN1v/1zdf/9c7X//XQ2f/1z9n/9dHa//XR2v/10dr/9tLb//bS2//30tv/+NLb//jU3P/41d7/+d7k//vs8P/swsv/3o2g/7YiSP+tCTDsqQA2EAAAAADUDT1M0QU5/dYvWv/kw8z/6+rp/+vq6//r6ur/6+nq/+vp6v/r6er/7ejp/+zp6v/s6er/7Onq/+zp6v/s6er/7enq/+3p6v/t5+r/7efo/+3n6P/u5+n/7efp/+7o6v/u5+n/6NPZ/9edq/+6Jkr/rQIu+64FM0kAAAAAAAAAAAAAAADUCzxM0wc779IIOf/UOWD/12OA/9lqg//ZaIT/1miD/9Vngf/VZ4H/1GWC/9RlgP/TZID/0mSA/9Bkf//RZH7/z2N+/85jfP/PYX3/zmF7/81gfP/LX3r/ymB7/8hadf/AMVX/swAt/7EDLe2wBi9KAAAAAAAAAAAAAAAAAAAAAAAAAADJEEcV1g9AeNINP8HSDj/r0g1A8tAMPvLQDD/yzww+8swLPfLLCzvyzAs78soKOvLICjryxgo58sYKN/LECjjywgk28sIJN/LBCTXyvQc18rwINPK7BzPyuQc06rcHM8C5BzJ1ww0qEQAAAAAAAAAAAAAAAA=="
  },
  INF: {
    type: "Inflow",
    id: 18,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A9PPzIO/v7yzv7+8s7+/vLO/v7yzv7+8s7u7vLLjc8F4urPrRLaX40i2f9tItmfTSLZPz0i2P8dItjfDSLY3w0i2N8NItje/SosXqbujq7Czr6uos6+rqLOvq6izr6uos6+rqLO3s7Cj///8A////AP///wD///8A////AP7+/gOmoaH8sKys/7CsrP+wrKz/sKys/7CsrP+wrKz/ZqjO/ym7/P9P1Pv/TtL7/07Q+v9Oz/r/Ts76/07N+f9Ozfn/Ts35/zGl8/9MhcL/mpaW/5qWlv+alpb/mpaW/5qWlv+alpb/jYqK/+jn5zL///8A////AP///wD///8A/f39Baahof/V0NH/0MvM/9DLzP/Qy8z/0MvM/9DLzP94vOH/McP9/zjN/f8vyf3/L8n9/y/J/f8vyf3/L8n9/y/J/f80y/3/Oa/0/2af3P/Qy8z/0MvM/9DLzP/Qy8z/0MvM/9DLzP+fm5v/5OPjOv///wD///8A////AP///wD9/f0FpqKi//Xz8//08vL/9PLy//Ty8v/08vL/9PLy/43T9/8xxf3/OtH9/zHM/f8xzP3/Mcz9/zHM/f8xzP3/Mcz9/zbP/f85sPT/eLLv//Ty8v/08vL/9PLy//Ty8v/08vL/9PLy/6Ofn//k4+M6////AP///wD///8A////AP7+/gOoo6P2q6am/6umpv+rpqb/q6am/6umpv+rpqb/Y6fL/yrB/f9T3Pz/VuD8/z3a/f862f3/Otn9/z7b/P9W3fv/UtX6/zKp8/9Igb7/ko6O/5KOjv+Sjo7/ko6O/5KOjv+Sjo7/jIiI/urq6i3///8A////AP///wD///8A////APv7+wv4+PgT+Pj4E/j4+BP4+PgT+Pj4E/j4+BPB4/VPLrj+0SO1/twhvP7/ZOz9/1/r/f9f6/3/Zez8/xuh9v8llfTaLZPy0qrN72H19vcT9vb2E/b29hP29vYT9vb2E/b29hP4+PgP////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A3fP/IhOt/e8Jqfv/DKn9/wqi+v8ImvX/E5n27uPy/hz///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A1eLpTrq2tv/59/f/19TU/66qqv/S3ORQ////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD79vQN9+vnHfv29A3///8A////AP///wDk4uJNrKin/8C9vf+3s7P/o5+f/9/e3k7///8A////AP///wD79vQN9+vnHfv29A3///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A/Pf1DNypmH/IeWDD8NvUNP///wD///8A////APv7+wrg399W1LeuhdbAuXre3NxW+/v7Cv///wD///8A////APDb1DTIeWDD3KmYf/z39Qz///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP35+AjdrJ5204pW6dCCSP/hua1j////AP///wD///8A////APft6hrCaknkynteyfz5+An///8A////AP///wD///8A4bmtY9CCSP/Tilbp3ayedv35+Aj///8A////AP///wD///8A////AP///wD///8A////AP///wD68/IQ4rioa899TvTmoWb/4Zpe/9GTgZv//v4B////AP///wD///8A1p2OiduWVP/WjFD64LOmbP///wD///8A////AP/+/gHRk4Gb4Zpe/+ahZv/PfU704rioa/rz8hD///8A////AP///wD///8A////AP///wD///8A/fn4CN6xoXHRg1Pt4pdj/+iTcf/nmmr+zodoxPnx8BL///8A////AO7Y1DPNf1fh6J9q/+ObY//Ogl7R+O/sF////wD///8A+fHwEs6HaMTnmmr+6JNx/+KXY//Rg1Pt3rGhcf35+Aj///8A////AP///wD///8A////AP77+wXcrJx21I1c4OOWZP/jjGz/5odz//Gkdf/Qg1Xu6s/KPv///wD///8AzIZzrOScYP/pkXH/445r/9qQVP/Vm4iR////AP///wDqz8o+0INV7vGkdf/mh3P/44xs/+OWZP/UjVzg3Kycdv77+wX///8A////AP///wD58O4U3q+gc9CEU+7lmWb/5oxw/+aJcf/rjXT/9aN7/9ySWP/ZqaBy/fr6Bt+3s1rRhlXv8qd1/+qMdP/ihm3/5Jhm/9CFWODs0co//fr6BtmpoHLcklj/9aN7/+uNdP/miXH/5oxw/+WZZv/QhFPu3q+gc/nw7hT///8A9urnHdyrmn3Ui1np555q/+mQc//nh3L/65F1/+6Ud//0nnr/6qNp+8qHdan16ukax35lw+ulaf/0nnv/7JB1/+aJcf/ljW7/3pVa/9GPdaz9+/sFyod1qeqjafv0nnr/7pR3/+uRdf/nh3L/6ZBz/+eeav/Ui1np3Kuaffbq5x3lwbdXxnJP4dmRUv/qqmj/6pNx/+yPdf/wlnf/75R3//ObeP/xpm//yX9g0suOiYzViFP/9qh2//GXeP/ulHb/6o90/+WHcP/mlmv/0YNO+NqonnPJf2DS8aZv//ObeP/vlHf/8JZ3/+yPdf/qk3H/6qpo/9mRUv/Gck/h5cG3V/Hd1zHUmIiRwnBewc1/TfTuoG//8JZ6//GUeP/ymHb/8aBx//awcP/ShFP1u2NM4++saP/ynnT/75R1//CWd//uk3b/6Ipy/+iTcf/koGT/wW9V1NKFVPT2sHD/8aBx//KYdv/xlHj/8JZ6/+6gb//Nf030wnBewdSYiJHx3dcx////AP///wDpzsdDzX1V6PKkdf/ymHr/8Zd3//CecP/ck1f/3JhX+85/Sv+yUTf/3ptW/+ikYv/xnHP/8ZV3/++Uef/vmnT/56Nj/92aWP+1Uzb/zn9K/9yYV/vck1f/8J5w//GXd//ymHr/8qR1/819VejpzsdD////AP///wD///8A/vz8BN61qmfYi1zz96d7//GVd//wl3H/55ll/sJzVdq3ZWWzsVFF5a5OSN21XlrEyXZL9/Cgbv/xlnb/8ph6//Cicv/Jdkrxw3Niu7NUR9+0V0ngt2Vls8JzVdrnmWX+8Jdx//GVd//3p3v/2Itc8961qmf+/PwE////AP///wD79vYL0ZeEmuKWY/v1n3f/7ZFw/+2Ya//ai1f/0ZeKkvny8g/05uUf7tvaLefLyj/MgFvg7Jxp/+6Tcf/ymHn/8aNz/8+HZc716OYe7tvaLfTm5R/58vIP0ZeKktqLV//tmGv/7ZFw//Wfd//ilmP70ZeEmvv29gv///8A//7+AfPl4yHMhWjF7KBr/e6Wb//nimf/6Zdk/89+TfzWpqFy+vX1DP///wD///8A5MbFRcl8V+Tnl2P/6o9s//GXdf/xo3L/zYVh0/Hg3if///8A////APr19QzWpqFyz35N/OmXZP/nimf/7pZv/+yga/3MhWjF8+XjIf/+/gH+/fwD5MS/Tc+AWenwoW3/5otm/+GFXP/gjlr+x3lV5OTFxUX+/f0C////AP///wDkxcVFyHpV5OSTXv/mimX/7pNw//CjcP/Ng2HT8eDeJ////wD///8A/v39AuTFxUXHeVXk4I5a/uGFXP/mi2b/8KFt/8+AWenkxL9N/v38A/38/ATYqJ531odX+OyZaP/ggVv/3YNV/9aFTv/HgWy78ODhJP///wD///8A////AOTFxUXHeVXk345Y/+GFXf/pj2r/7qFs/82CYdPx4N4n////AP///wD///8A8ODhJMeBbLvWhU7/3YNV/+CBW//smWj/1odX+Nionnf9/PwE+vPzDs2Ne6fdkFv744xe/9d4Uf/ZhE7/zn1I/82SiZH47/AS////AP///wD///8A5MXFRcV3U+TcilH/3H9X/+WKYv/rnWj/y4Fh0/Hg3if///8A////AP///wD47/ASzZKJkc59SP/ZhE7/13hR/+OMXv/dkFv7zY17p/rz8w7v3Nsrx3te1d6NWf7XeVH/0HJI/9eES//GdEn22KuqZ/v39wn///8A////AP///wDjxMVFxHZT5NeGTf/WeU//4IRb/+eZYv/KgGDT8d/eJ////wD///8A////APv39wnYq6pnxnRJ9teES//Qckj/13lR/96NWf7He17V79zbK922s1zNf1Lw66le/9mDTv/PdET/0X9I/sN1WNrny807////AP///wD///8A////AOPDxUXDdFLk1YNJ/9F0Sf/aflX/45Ve/8h+X9Pw394n////AP///wD///8A////AOfLzTvDdVja0X9I/s90RP/Zg07/66le/81/UvDdtrNc2KuoarJQOP/KeUj/0oZK/+CbUf/ZkE3/xH9wtfLj5B////8A////AP///wD///8A48PFRcN0U+TTf0f/zW1D/9R1TP/ej1f/yHxf0/Df3if///8A////AP///wD///8A8uPkH8R/cLXZkE3/4JtR/9KGSv/KeUj/slA4/9irqGr///8A8uLfKN60qm3JiHiqs1c9+LBPOP/LkZCI+PHxEP///wD///8A////AP///wDhwMJIw3RT5eGeUv/el1D/4ZtU/+WjWv/GeV7U793dKP///wD///8A////AP///wD48fEQy5GQiLBPOP+zVz34yYh4qt60qm3y4t8o////AP///wD///8A////AP///wD///8A7NXTN+zY2S79/PwE////AP///wD///8A////AOfNzzqxV1HWsVE6/bVaQfS3XEL0s1M5/7tpYMTz5uUf////AP///wD///8A////AP38/ATs2Nku7NXTN////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  LEV: {
    type: "Level",
    id: 17,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wBKTUpCWl1axlpdWsZaXVrGWl1axlpdWsZaXVrGWl1aa////wD///8A////AP///wD///8A////AP///wD///8AAAAAAAAAAAD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AEpNSntjYWP/a21r/2tta/9rbWv/a21r/2NlY/9aXVq9////AP///wD///8A////AP///wD///8A////AP///wAAAAAAAAAAAP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8ASk1Ke2tta/+cnpz/nJqc/5yanP+cnpz/e317/1pdWr3///8A////AP///wD///8A////AP///wD///8A////AAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wBKTUp7a21r/5SSlP+EhoT/jIqM/5SSlP97fXv/Wl1avf///wD///8A////AP///wD///8A////AP///wD///8AAAAAAAAAAAD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AEpNSntrbWv/lJKU/4SChP+Mioz/lJKU/4SChP9aXVq9////AP///wD///8A////AP///wD///8A////AP///wAAAAAAAAAAAP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8ASk1Ke2tta/+UkpT/jIqM/4yKjP+clpz/hIKE/1pdWr3///8A////AP///wD///8A////AP///wD///8A////AAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wBKTUp7a21r/5SWlP+Mioz/lJKU/5yWnP+EgoT/Y2Fjvf///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AEpNSntrbWv/lJaU/4yOjP+UkpT/pZ6l/4SGhP9jZWO9////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8ASk1Ke2tta/+cmpz/lJKU/5SWlP+loqX/hIaE/2NlY73///8A////AP///wD///8AxoIpCM6GKQjOhikIzoYpCMaCKQi9eSkIvXkpCLV1IQitcSEIrXEhCKVtIQilbSEIpWkhCJxpIQj///8A////AP///wD///8A////AP///wBKTUp7a21r/5yenP+UlpT/nJ6c/6Wipf+Mioz/Y2Vjvf///wD///8A1pI5ENaWQkLWlkJr1pZCe9aWQnvWlkJ71pI5e86KKXvOhil7zoYpe86GKXvGgil7xoIpe719KXu9fSl7tXUha61xIUKtbSEY////AP///wD///8A////AEpNSntrbWv/nJ6c/5yanP+cnpz/paql/4yKjP9raWu9////AN6qYyHenlJr3qJSxt6iUufeolrv3p5S79aaSu/Wmkrv1pI579aOMe/Wiinvzoop786KKe/OiinvzoYp786GKe+9eSnnpW0hlKVpITH///8A////AP///wD///8ASk1Ke2tta/+lnqX/nJ6c/6Wmpf+tqq3/jI6M/2tpa73nuoQ557JzjN6uc9bermv/3q5r/96qY//eplr/3qJa/9aaSv/Wkjn/1pI5/9aOMf/Wiin/1oop/9aKKf/Ohin/1o4x/86GKfe9eSmctXUhOf///wD///8A////AP///wBKUUp7a21r/6Wmpf+loqX/paal/62urf+Mjoz/jIJzzue6hKXnsnPv3q5z/96uc//ermv/3qZj/96iWv/eolr/1ppK/9aaSv/WlkL/1o4x/9aKKf/Wiin/1oop/86GKf/WjjH/zoYp97V1IZy1dSE5////AP///wD///8A////AEpRSntzcXP/raqt/6Wmpf+trq3/ta6t/62ahP/GonPv57Jz/+eyc//nsnP/3q5r/96qY//eqmP/3qJa/96eUv/Wmkr/1pI5/9aSOf/WjjH/1oop/9aKKf/Wiin/1oop/9aOMf+9eSn3nGkhpZxpITn///8A////AP///wD///8ASlFKe3Nxc/+tqq3/raqt/62urf/Grpz/zqZz/96ua//ermv/3q5r/96ua//eplr/3qJS/96eUv/enlL/1pI5/9aOMf/WjjH/1oop/8Z9Kf/GfSn/xn0p/8Z9Kf/GfSn/zoYp/7V5KfecaSGlnGUhOf///wD///8A////AP///wBSVVJ7c3Fz/62urf+trq3/tbK1/8amhP/OllL/3p5K/9aaSv/Wkjn/1o4x/8aCKf+9fSn/vXkp/715Kf+1eSn/tXUh/61xIf+tcSH/rXEh/5xpIf+caSH/nGUh/5xlIf+laSH/nGkh95xlIZycZSE5////AP///wD///8A////AFJVUntzcXP/ra6t/7Wytf+1srX/ta6t/6WSc/+9hkLv1pI599aSOf/Wiin/vX0p/715Kf+9eSn/tXUh/7V1If+1dSH/rXEh/61xIf+tcSH/nGkh/5xpIf+cZSH/nGUh/6VpIf+caSH3lGEhnIxdGDn///8A////AP///wD///8AUlVSe3t5e/+1srX/tbK1/7Wytf+1srX/lJKU/4x1Ws61eSmUvX0p3saCKf+9fSn/vXkp/715Kf+1dSH/tXUh/61xIf+tcSH/rXEh/6VtIf+caSH/nGkh/5xlIf+caSH/pWkh/5xlIfeUYSGljF0YOf///wD///8A////AP///wBaWVp7e3l7/7Wytf+1srX/tbK1/7Wytf+UkpT/c3FzvaVtISmtcSF7rXEhzrV1If+1dSH/tXUh/7V1If+tcSH/rXEh/61xIf+caSH/nGkh/5xpIf+caSH/nGUh/5xlIf+laSH/nGUh94xdGJyMXRg5////AP///wD///8A////AFpZWnt7eXv/tbK1/7Wytf+1srX/tbK1/5SSlP9zcXO9////AKVpIRilaSFarXEhva1xIeetcSHvrXEh761xIe+lbSHvnGkh75xlIe+cZSHvlGEh75RhIe+UYSHvlGEh75xlIe+UYSHnjF0YlIxdGCn///8A////AP///wD///8AWllae3t5e/+1srX/tbK1/7Wytf+trq3/lJKU/3Nxc73///8A////AJxlIQicZSE5nGUhWpxlIWucaSFznGUhc5xlIXOUYSFzlGEhc5xlIXOcZSFzlGEhc5RhIXOUYSFznGUhc5RhIWOMXRhCjF0YEP///wD///8A////AP///wBaWVp7e317/7W2tf+1srX/ra6t/62qrf+UkpT/c3Fzvf///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AFpdWnt7fXv/tba1/62urf+tqq3/raqt/5SSlP9zcXO9////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AWl1ae4SChP+1srX/ra6t/62qrf+lqqX/lJKU/3Nxc73///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wBaXVp7hIKE/7Wutf+tqq3/paal/6Wipf+Mjoz/c3Fzvf///wD///8A////AP///wD///8A////AP///wD///8AAAAAAAAAAAD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AGNhY3uEgoT/ra6t/6Wmpf+loqX/nKKc/4yOjP9zcXO9////AP///wD///8A////AP///wD///8A////AP///wAAAAAAAAAAAP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AY2Fje4SChP+trq3/paal/6Wipf+copz/jI6M/3Nxc73///8A////AP///wD///8A////AP///wD///8A////AAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wBjYWN7hIKE/62urf+lqqX/paal/6Wmpf+Mjoz/c3Fzvf///wD///8A////AP///wD///8A////AP///wD///8AAAAAAAAAAAD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AGNhY3t7eXv/hIKE/4SChP+EgoT/hIKE/3t5e/9zcXO9////AP///wD///8A////AP///wD///8A////AP///wAAAAAAAAAAAP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AY2FjOXNxc71zcXO9c3FzvXNxc71zcXO9c3FzvXNxc2P///8A////AP///wD///8A////AP///wD///8A////AAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AAAAAAAAAAAD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  PSD: {
    type: "Pipe Sediment Data",
    id: 56,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AAYO5MwGDuYEBg7m5AYO53gGDufABg7nwAYO53gGDubkBg7mBAYO5M////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wABhrsBAYW7WAGFu9EBhbv/EIKw/zJ8l/9HeIf/UnZ//1J2f/9HeIf/MnyX/w+Csf8Bhbv/AYW70QGFu1gBhrsB////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AAYi9IQGHvMEBh7z/LX6c/2hzcP+IbFj/iWxY/4lsWP+JbFj/iWxY/4lsWP+JbFj/iGxY/2hzcP8tfpz/AYe8/wGHvMEBiL0h////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AAKKvz8Cir7tFoav/2Z1c/+Db13/g29d/4NvXf+Db13/g29d/4NvXf+Db13/g29d/4NvXf+Db13/g29d/4NvXf9mdXP/Foav/wKKvu0Cir8/////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wACjcE/Ao3A9ieFpP93c2j/fXJj/31yY/99cmP/fXJj/31yY/99cmP/fXJj/31yY/99cmP/fXJj/31yY/99cmP/fXJj/31yY/93c2j/J4Wk/wKNwPYCjcE/////AP///wD///8A////AP///wD///8A////AP///wD///8AA5DDIQOQw+0miKj/dHVs/3Z1av92dWr/dnVq/3Z1av92dWr/dnVq/3Z1av92dWr/dnVq/3Z1av92dWr/dnVq/3Z1av92dWr/dnVq/3Z1av90dWz/JYio/wOQw+0DkMMh////AP///wD///8A////AP///wD///8A////AAOUxwEDk8bBFY+5/2p6dv9veHL/b3hy/294cv9veHL/b3hy/294cv9veHL/b3hy/294cv9veHL/b3hy/294cv9veHL/b3hy/294cv9veHL/b3hy/294cv9qenb/FY+5/wOTxsEDlMcB////AP///wD///8A////AP///wD///8ABJfJWASXyf9Rg4v/Z316/2d9ev9nfXr/Z316/2d9ev9nfXr/Z316/2d9ev9nfXr/Z316/2d9ev9nfXr/Z316/2d9ev9nfXr/Z316/2d9ev9nfXr/Z316/2d9ev9Rg4v/BJfJ/wSXyVj///8A////AP///wD///8A////AP///wAFmszRIpK0/2CBgv9ggYL/YIGC/2CBgv9ggYL/YIGC/2CBgv9ggYL/YIGC/2CBgv9ggYL/YIGC/2CBgv9ggYL/YIGC/2CBgv9ggYL/YIGC/2CBgv9ggYL/YIGC/2CBgv8jkrP/BZrM0f///wD///8A////AP///wD///8ABZ7ONQaezv9Fi5r/WYaK/1mGiv9Zhor/WYaK/1mGiv9Zhor/WYaK/1mGiv9Zhor/WYaK/1mGiv9Zhor/WYaK/1mGiv9Zhor/WYaK/1mGiv9Zhor/WYaK/1mGiv9Zhor/WYaK/0WLmv8Gns7/BZ7ONf///wD///8A////AP///wAGotGBDqDK/1CLk/9Qi5P/UIuT/1CLk/9Qi5P/UIuT/1CLk/9Qi5P/UIuT/1CLk/9Qi5P/UIuT/1CLk/9Qi5P/UIuT/1CLk/9Qi5P/UIuT/1CLk/9Qi5P/UIuT/1CLk/9Qi5P/UIuT/w6gyv8GotGB////AP///wD///8A////AAem1Lkdn8H/SZCc/0mQnP9JkJz/SZCc/0mQnP9JkJz/SZCc/0mQnP9IkZ3/P5Sk/zaWq/8ymLD/Mpiw/zaWq/8/lKT/SJGd/0mQnP9JkJz/SZCc/0mQnP9JkJz/SZCc/0mQnP9JkJz/HZ/B/wem1Ln///8A////AP///wD///8ACKrX3iKhwP9BlqX/QZal/0GWpf9BlqX/QZal/zWasP8moL3/F6XK/wup1P8Iqtf/CKrX/wiq1/8Iqtf/CKrX/wiq1/8LqdT/F6XK/yagvf81mrD/QJem/0GWpf9BlqX/QZal/0GWpf8jocD/CKrX3v///wD///8A////AP///wAJr9vwEK3V/yyivP8uorv/JaXC/xmpzP8Mrtj/Ca/b/wmv2/8Jr9v/Ca/b/wmv2/8Jr9v/Ca/b/wmv2/8Jr9v/Ca/b/wmv2/8Jr9v/Ca/b/wmv2/8Mrtj/GanM/yWlwv8uorv/LaK7/xCt1f8Jr9vw////AP///wD///8A////AAmz3vAJs97/CbPe/wmz3v8Js97/CbPe/wmz3v8Js97/CbPe/wmz3v8Js97/CbPe/wmz3v8Js97/CbPe/wmz3v8Js97/CbPe/wmz3v8Js97/CbPe/wmz3v8Js97/CbPe/wmz3v8Js97/CbPe/wmz3vD///8A////AP///wD///8ACrbh3gq34f8Kt+H/Crfh/wq34f8Kt+H/Crfh/wq34f8Kt+H/Crfh/wq34f8Kt+H/Crfh/wq34f8Kt+H/Crfh/wq34f8Kt+H/Crfh/wq34f8Kt+H/Crfh/wq34f8Kt+H/Crfh/wq34f8Kt+H/Crbh3v///wD///8A////AP///wALuuS5C7vk/wu75P8Lu+T/C7vk/wu75P8Lu+T/C7vk/wu75P8Lu+T/C7vk/wu75P8Lu+T/C7vk/wu75P8Lu+T/C7vk/wu75P8Lu+T/C7vk/wu75P8Lu+T/C7vk/wu75P8Lu+T/C7vk/wu75P8Lu+S5////AP///wD///8A////AAu+5oEMv+f/DMDn/wzB6P8Mwuj/DMLo/wzC6P8Mwuj/DMLo/wzC6P8Mwuj/DMLo/wzC6P8Mwuj/DMLo/wzC6P8Mwuj/DMLo/wzC6P8Mwuj/DMLo/wzC6P8Mwuj/DMLo/wzB6P8MwOf/DL/n/wu/5oH///8A////AP///wD///8ADMLpNQzD6v8Mxer/C8nr/wvL6/8Ly+v/C8vr/wvL6/8Ly+v/C8vr/wvL6/8Ly+v/C8vr/wvL6/8Ly+v/C8vr/wvL6/8Ly+v/C8vr/wvL6/8Ly+v/C8vr/wvL6/8Ly+v/C8nr/wzF6v8Mw+r/DMLpNf///wD///8A////AP///wD///8ADcfs0Q3J7f8Mzu7/C9Pv/wvU7/8L1O//C9Tv/wvU7/8L1O//C9Tv/wvU7/8L1O//C9Tv/wvU7/8L1O//C9Tv/wvU7/8L1O//C9Tv/wvU7/8L1O//C9Tv/wvT7/8Mzu7/Dcnt/w3H7NH///8A////AP///wD///8A////AP///wANyu5YDszv/w3Q8P8L2PH/C9zx/wvc8f8L3PH/C9zx/wvc8f8L3PH/C9zx/wvc8f8L3PH/C9zx/wvc8f8L3PH/C9zx/wvc8f8L3PH/C9zx/wvc8f8L3PH/C9jx/w3Q8P8OzO//DcrvWP///wD///8A////AP///wD///8A////AA7M8AEOz/LBD9Hy/w3Y8/8L4PP/CuPz/wrj8/8K4/P/CuPz/wrj8/8K4/P/CuPz/wrj8/8K4/P/CuPz/wrj8/8K4/P/CuPz/wrj8/8K4/P/CuPz/wvg8/8N2PP/D9Hy/w7P8sEOzfAB////AP///wD///8A////AP///wD///8A////AA/Q8yAP0vTtDtb0/wze9P8K5vT/Cej1/wnp9f8J6fX/Cen1/wnp9f8J6fX/Cen1/wnp9f8J6fX/Cen1/wnp9f8J6fX/Cen1/wno9f8K5vT/DN70/w7W9P8P0vTtD9HzIf///wD///8A////AP///wD///8A////AP///wD///8A////AA/U9T8Q1ff1D9n3/wzh9v8K6fb/Cez2/wnt9v8J7vb/Ce72/wnu9v8J7vb/Ce72/wnu9v8J7vb/Ce72/wnt9v8J7Pb/Cun2/wzh9v8P2ff/ENX39Q/U9j////8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////ABDX+D8Q2PntD9v5/w3h+P8L6Pf/Ce33/wnw9/8I8fb/CPH2/wjx9v8I8fb/CPH2/wjx9v8J8Pf/Ce33/wvo9/8N4fj/D9v5/xDY+e0Q1/g/////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////ABDZ+SER2vrBEdz7/w/f+v8N5Pn/DOn5/wrt+P8K7vj/Ce/3/wnv9/8K7vj/Cu34/wzp+f8N5Pn/D9/6/xHc+/8R2vrBENn5If///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////ABHb+wER3PxYEd380RHe/P8Q3/v/D+L7/w/j+/8O5Pr/DuT6/w/j+/8P4vv/EN/7/xHe/P8R3fzREdz8WBHb+wH///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AEd79MxLe/YES3/65Et/+3hLf/vAS3/7wEt/+3hLf/rkS3v2BEd79Mv///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  PGR: {
    type: "Pollutograph",
    id: 54,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AUBV9AVAVfXpRFX7mURV//1IVgP9TFoH/UxaC/1QWg/9UFoP/VBaD/1QWg/9UFoT/VBaE/1QWhP9UFoT/VBaE/1QWhP9UFoT/VBaE/1QWg/9UFoP/VBaD/1QWg/9TFoL/UxaB/1IVgP9RFX//URV+7VAVfY5QFX0G////AP///wBQFX10TxV7/0kTc/9JE3P/ShN1/0wUd/9NFHj/TRR5/04Uev9OFHr/ThR6/04Uev9OFHr/ThR6/04Uev9OFHr/ThR6/04Uev9OFHr/ThR6/04Uev9OFHr/TRR5/00UeP9MFHf/SxR1/0kTc/9JE3P/ThR7/1AVfZT///8A////AFEVftpKE3X/UxaB/1oYjf9eGJP/XxmV/2EZmP9hGZj/YRmZ/2Iamf9jGpr/Yxqa/2Mamv9jGpv/Yxqb/2Mam/9jGpv/Yxqa/2Mamv9jGpr/Yxqa/2Iamf9hGZn/YRmY/2AZlv9eGZP/WxiP/1QWhP9KE3T/URV+9lEVfgT///8AURV+7k4Ue/9aGI3/XxmU/2EZmP9jGpr/ZBqc/2Qanf9lGp7/ZRqe/2Uan/9lGp//Zhuf/2Ybn/9mG5//Zhuf/2Ybn/9mG5//Zhuf/2Uan/9lGp//ZRqe/2Qanf9kGp3/Yxqa/2EZmf9fGZX/WxiP/08VfP9QFX3/URV+EP///wBRFX/uUhWA/10Ykf9gGZf/hk+v/8y13//ez+v/4NHs/93O6f/Qwdv/yLnU/8i50//IudP/yLnT/8i50//IudP/yLnT/8i50//IudP/yLnT/8i50//IudP/yLnT/8a30v+4oMr/gEqo/2EZmP9dGJL/UxaC/1EVfv9RFX4Q////AFIVgO5TFoL/XhiT/2EZmf9mHp3/p37H/9rI5//f0Ov/39Dr/9rK5f/Ovtr/x7jT/8e30v/Ht9P/x7fT/8e30//Ht9P/x7fT/8e3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4f+jUeH/olDh/6JP4f+hTuH/oU7g/6BM4P+fSeD/Zxuh/1IVgRD///8AVBaE159J4P+iT+H/olDh/6NS4f+kU+H/pFPh/6RT4v+kU+L/pFPi/6RT4v+kU+L/pFPi/6RT4v+kU+L/pFPi/6RT4v+kU+L/pFPi/6RT4v+kVOL/pFPi/6RT4v+kU+H/pFPh/6NS4f+jUeH/ok/h/6FO4P9cGJDzUhWBA////wBTFoJqdB62/6FO4f+lVeL/pVXi/6ZX4v+mV+L/plfi/6ZY4v+mWOL/plji/6ZY4v+mWOL/plji/6ZY4v+mWOL/plji/6ZY4v+mWOL/plji/6ZY4v+mWOL/plfi/6ZX4v+mV+L/pVbi/6VV4v+jUuH/fiHF/1QWhIr///8A////AP///wBUFoRoVRaF110YkutdGJLrXhmT618ZlOtfGZXrXxmV618ZletfGZXrXxmV618ZletfGZXrXxmV618ZletfGZXrXxmV618ZletfGZXrXxmV618ZletfGZXrXxmU614Zk+teGJPrXRiS61cXh91UFoR8VBaDA////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  RAIN: {
    type: "Rainfall Event",
    id: 13,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wASAAADEwAACRYAAA0XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFgAADRMAAAgSAAAC////AP///wD///8AEQAAARMAAA8VAAApMQwHQk8ZDlRPGQ5UTxkOVE8ZDlRQGQ5UUBkOVFAZDlRQGQ9UUBkPVFAZD1RQGQ9UUBkPVFAZD1RQGQ9UUBkPVFAZDlRQGQ5UUBkOVE8ZDlRPGQ5UTxkOVE4ZDlMpCQU+FAAAJhMAAA0RAAAB////AP///wAUAAADRxYNKJs7Ib2wRCf8sUUn/7FFJ/+zRSf/tkYo/7hHKf+6SCn/ukgp/7pIKf+7SCn/u0gp/7tIKf+7SCn/u0gp/7tIKf+6SCn/ukgp/7lIKf+4Ryn/tUYo/7NFJ/+xRSf/sUUn/69EJ/mWOSCsMAwHHBQAAAL///8A////ABQAAAOqQiW2sUUn/7FFJ/+0Rij/ukgp/79KKv/DTCv/xk0s/8hNLP/JTiz/yU4t/8pOLf/KTi3/yk4t/8pOLf/KTi3/yk4t/8lOLf/JTiz/yE0s/8ZNLP/DSyv/vkoq/7lIKf+zRij/sUUn/7FFJ/+oQSWXFAAAAv///wD///8ArEMmIbFFJ/6xRSf/tkYo/75KKv/GTCz/zE8t/9BQLv/TUi//1VIv/9ZTL//WUy//1lMv/9ZTL//WUy//1lMv/9ZTL//WUy//1lMv/9ZTL//VUi//01Ev/9BQLv/LTi3/xUwr/71JKv+1Rij/sUUn/7FFJ/axRScI////AP///wCxRSc+sUUn/7RGKP++Sir/yE0s/9BQLv/WUy//21Qw/95WMf/gVzL/4Vcy/+FXMv/hVzL/5W9P/+6fiv/0wbP/9s7D//XFuP/vpZH/5nVW/+BWMv/eVjH/2lQw/9VSL//PUC7/x00s/71JKv+zRij/sUUn/7FFJx7///8A////ALFFJz+xRSf/u0gp/8ZNLP/QUC7/2FMw/99WMf/kWDL/51kz/+laNP/qWzT/6ls0//KWff/85N7////////////////////////////86+b/86WQ/+dcNv/jWDL/3lYx/9dTMP/PUC7/xUwr/7lIKf+xRSf/sUUnH////wD///8AsUUnP7RGKP/ASiv/zE8t/9ZTL//fVjH/5lkz/+tbNP/vXDX/8V01//JfN//5uqj/////////////////////////////////////////////////+s7C/+tiPf/lWDP/3lYx/9VSL//LTi3/vkoq/7NFJ/+xRScf////AP///wCxRSc/t0co/8VMK//RUS7/21Uw/+RYM//rWzT/8V01//RfNv/3Xzf/+6aQ//////////////n4//3Pw//7noX/+ops//ubgv/9zsL/////////////////+b2t/+pbNP/jWDL/2lQw/9BQLv/DSyv/tUYo/7FFJx////8A////ALJFJz+5SCn/yE0s/9RSL//fVjH/6Foz/+9dNf/1Xzb/+WI5//yXfP//+Pb////////////9v6//+2E4//thOP/7YTj/+2E4//thOP/8lXr///f1////////////84dr/+dZM//eVjH/01Ev/8ZNLP+4Ryn/skUnH////wD///8As0UnP7tJKf/KTi3/11Mv/+FXMv/qWzT/8V41//htR//+1Mj/////////////////////////////1Mn//nFM//5iOf/+Yjn//mI5//5iOf/+qZL////////////6xLX/6Vo0/+BWMv/VUi//yE0s/7lIKf+0RScf////AP///wC0RSg/vEkq/81VNP/caUr/5nFR/+94WP/1g2X//eLa///////96eX/+7em//6okf//tqL//+ji////////4Nj//25H//9jOf//Yzn//2M5//5rRP//7+v///////3m3//qWzT/4Vcy/9ZTL//JTiz/ukgp/7RGKB////8A////ALRGKD+8SSr/z1s8/+B2Wv/ofF7/8IFj//q/r///////6c/U//uUev//k3b//5Z5//+Yff/+oIf/8tra////////uab//2M5//9jOf//Yzn//mI5//7Yzv///////vb0/+pbNP/hVzL/1lMv/8lOLf+6SCn/tUYoH////wD///8AtEYoP7xJKv/PXT7/4Xpf/+mBZP/whWn//ufh///////vnpH//pV5//+YfP//mn///52C//+ghv/2s6T//v7////x7f//nIH//3pX//9jOf/+Yjn//tzT///////+8Oz/6ls0/+FXMv/WUy//yk4t/7tIKf+1Rigf////AP///wC0Rig/vEkq/9BgQv/if2X/6oVp//GKbv/+8/D///z8//2ehP/+mX7//5yB//+fhf//oYj//6SL//yrl//+/Pz//vz7//6zn///sZz//6SL//6Lbf//+Pb///////vQxf/qWzT/4Vcy/9ZTL//KTi3/u0gp/7VGKB////8A////ALRGKD+8SSr/0WNF/+OEav/rim//8Y50//7w7P/+/f7//KaQ//6ehP//oYf//6OL//+mjv//qJH//LSh///+/f/9+Pf//rWi//+1of//t6T//+Td////////////95uC/+pbNP/hVzL/1lMv/8pOLf+7SCn/tUYoH////wD///8AtEYoP7xJKv/SZkn/5Ihw/+uOdf/yk3n//NbM///////wv7v//qOK//+ljf//qJD//6qT//+tl//yy8f////////n4P//t6T//7mm///Yzv////////////7u6v/zcEv/6ls0/+FXMv/WUy//yk4t/7tIKf+1Rigf////AP///wC0Rig/vEkq/9NqTf/ljXb/7JN6//KYgP/5rJj///v7//z5+//urqb//6mS//+slv//r5n//sW3///9/f///v7//8i6//+7qf//0sb///7+////////+/v//dDE//q8q//sa0j/4Vcy/9ZTL//KTi3/u0gp/7VGKB////8A////ALRGKD+8SSr/1G5S/+aSe//tmIH/852F//ihiv/9zL7///////zy8P/8sqD//7Gc//q5q//89fT////////e1P//vav//8W2///49v////////7+//7a0f/9y73/+8y///e/r//jYj//1lMv/8pOLf+7SCn/tUYoH////wD///8AtEYoP7xJKv/VcVX/55eC/+6dhv/0oYv/+KWP//upk//+2tH///////nVz///taH//+bg/////////////9jO///Bsf//4tr/////////////4Nj//sy///3Owv/70MX/+dHG//Gyof/WVDD/yU4t/7pIKf+1Rigf////AP///wC0RSg/vEkq/9Z2W//onIj/76GM//Smkf/5qpX/+66Z//60oP//8u//+/Ly//vCtP/+/Pv/////////////7+v//8m6///6+P///////+vm///Owv/+0cT//dLH//zUyf/61cv/+NbN/+OIb//JTiz/ukgp/7RGKB////8A////ALNFJz+7SSn/13pi/+mhjf/vppL/9KuX//mvm//7sp///bWi///KvP//+/r/+unn///9/f//1sv///bz///8+///4tr////////39f//08f//tLG//7Uyf/91sv//NfN//rZ0P/42tL/883D/8lRMf+6SCn/tEUnH////wD///8AskUnP7pIKf/Xf2f/6aWT/++qmP/0r5z/+LOg//q2pP/8uaf//byr///r5v///////+ji//7Gt//+3tb////////9/P///////t/W//7UyP/+1cv//dfN//zZ0P/729L/+tzU//jd1v/33tf/14Jr/7hHKf+zRScf////AP///wCxRSc/t0co/9eDbf/pqpn/7q6d//Oyof/3tqX/+bqp//u9rP/8wLD//dfM///////91cr//cq8//3Pw///+fj////////29P/91cr//dfN//3Zz//929H//NzT//ve1v/639j/+N/Z//fh2//hp5b/tkYo/7JFJx////8A////ALFFJz+0Rij/1YZx/+iunv/tsqL/8ren//W6qv/3va7/+cGx//rEtf/7zL///vHu//vNwf/7zcH/+9DE//7r5v///////enj//zYzv/82tD//NzT//zd1f/739f/+uDZ//nh2//4493/9+Pe/+GrnP+zRSf/sUUnH////wD///8AsUUnP7JFJ//UjXn/57Kk/+y2p//wu6z/872v//XBs//3xLb/+Me6//nMwP/62M//+c7D//nQxf/608j/++DZ///9/f/73tf/+9vS//vd1f/73tb/++DZ//ri2//649z/+ePe//jl4P/35uH/4rOm/7FFJ/+xRScf////AP///wCxRSc/sUUn/9GLeP/ltqn/6rqs/+69sP/xwbT/88S4//THu//2yr//9szB//fPxP/30cf/99PJ//jWzP/53NT//fDt//nc1P/53tb/+d/Y//rh2v/649z/+eTe//nl3//45uH/9+fi//fo4//erqH/sUUn/7FFJx////8A////ALFFJyexRSf/wWxU/+S5rf/ovbH/68G1/+7Euf/xyL3/8sq///PNw//0z8X/9dHI//XUy//21s3/9tjQ//fc1f/55N7/+N7X//jf2f/44dv/+OPd//jl3//45uH/+Ofi//jo5P/36OT/9ujk/8h8Z/+xRSf6sUUnDP///wD///8A////ALFFJ8GxRSf/w29Y/9ebi//dpZX/4aeY/+Oqm//lrJ3/566f/+iwof/osqT/6bSl/+m2qP/qt6n/6rmr/+u6rf/ru67/672w/+y9sf/svrL/67+0/+vAtP/pwLX/6MC1/+K2q//Jf2r/sUUn/7FFJ6L///8A////AP///wD///8AsUUnGbFFJ8GxRSf/sUUn/7JFJ/+0Rij/t0co/7pIKf+7SSn/vEkq/7xJKv+8SSr/vEkq/7xJKv+8SSr/vEkq/7xJKv+8SSr/vEkq/7tJKf+5SCn/t0co/7RGKP+xRSf/sUUn/7FFJ/6xRSeusUUnDf///wD///8A////AP///wD///8A////ALFFJyexRSc/sUUnP7FFJz+xRSc/s0UnP7RGJz+0Rig/tUYoP7VGKD+1Rig/tUYoP7VGKD+1Rig/tUYoP7VGKD+0Rig/tEYnP7NFJz+xRSc/sUUnP7FFJz+xRSc+sUUnIP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  REG: {
    type: "Regulator",
    id: 187,
    icon: "data:image/png;base64,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AAAAAAAAAAAAAP///wNAQED/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAEBAQP////8DAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////A0BAQP8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQEBA/////wMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///8DQEBA/wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABAQED/////AwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP///wNAQED/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAEBAQP////8DAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////A0BAQP8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQEBA/////wMAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///8DQEBA/wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABAQED/////AwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP///wNAQED/AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAIaGiJaAgICpjo6OqUBAQP+NjY2qgICAqYCAgKmAgICpgICAqYCAgKl/f38UAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA////A0BAQP+fn59zjY2NXtjY2BYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABAIAAAuaG9q6Gtxbf91cXP/QEBA/3Bwcv9rcW3/anFt/2txbf93dXP/gICA/3t7ex8AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAC8upqIQEBA/5GQgf+AgID/h4eH6KmpqSoAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAfVY6W9+WZf/hlmX/45Zl/+SWZf/dl2H/5JZl/+KWZf/ilmX/6Zxl/598Xf+AgIX/e3t7HwAAAAAAAAAAAAAAAAAAAAAAAAAAP0KxdhYgyv8ABcr/Hie5/3d2d/+AgID/jIyMzwAAAAAAAAAAAAAAAAAAAABzc3MqAAAAAAAAAAB9X0hb3qZ9/96mff/epn3/3qZ9/96mff/epn3/3qZ9/96mff/lpn3/ooRu/4CAgP97e3sfAAAAAAAAAAAAAAAAAAAAADdGrG4AIf//ACH//wAh//8AIf//ABzt/4J/cP+BgYH+eHh4OgAAAAAAAAAAAAAAAEBAQP8AAAAAAAAAAJB0YlvpvJT/5LeU/+S3lP/kt5T/5LeU/+S3lP/kt5T/5LeU/+y9lP+ljXv/gIaJ/4+Pjx8AAAAAAAAAAAAAAAAAAAAAF0Dc5gA4//8AOP//ADj//wA4//8AOP//RVib/5aUjfxAQED/AAAAAAAAAABAQED/QEBA/0BAQP9AQED/QEBA//TOs//qxqz/6sas/+rGrP/qxqz/6sas/+rGrP/qxqz/9c+0/39vYv9AQED/QEBA/0BAQP9AQED/QEBA/0BAQP8HRMv+AE///wBP//8AT///AE///wBP//8XM3T/QEBA/0BAQP9AQED/QEBA/wAAAABAQED/AAAAAAAAAACXh3tb9tbD//DWw//w1sP/8NbD//DWw//w1sP/8NbD//DWw//53cn/rJ6U/4CFhv+Ojo4fAAAAAAAAAAAAAAAAAAAAABti2NQAZf//AGX//wBl//8AZf//AGT//2B3m8f///YXQEBA/wAAAAAAAAAAAAAAAFRUVCEAAAAAAAAAAIyGfFv87uP/9ebb//Xm2//15tv/9ebb//Xm2//15tv/9ebb///v5P+4rqfUdnh6g5aWlg8AAAAAAAAAAAAAAAAAAAAAUXKgRwd38fsAe///AHv//wB7//8WddnXoGpGDAAAAABqamolAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAfHx7W9zX0//c19P/3NfT/9zX0//c19P/3NfT/9zX0//c19P/3NfT/6+qp6cAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAATXB/NCB9yKYWgNC/KHi1h6ibaxEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA=="
  },
  PTSEL: {
    type: "Results Analysis",
    id: 164,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD+/v4B/v7+Af39/QL9/f0C/f39Av39/QL8/PwD/Pz8A/z8/AP8/PwD/Pz8A/39/QL9/f0C/f39Av7+/gH+/v4B/v7+Af///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A/v7+Af39/QL5+fkG9fX1CvDw8A/s7OwT4+PjHMLCwj7BwcFBwsLCQ8PDw0TExMRFxMTERcTDw0TCwsJDwcHBQcHBwT/k5OQb6+vrFO/v7xDz8/MM+Pj4B/z8/AP+/v4B////AP///wD///8A////AP///wD///8A////AP///wD+/v4B/Pz8A/j4+Afz8/MM7e3tEunp6Rbc3NwjfXx8l0RDQ/1QT0/9WVhY/WBfX/9hYWH9WllZ/VBPT/1EQ0P9hYWFjN7e3iHo6OgX7OzsE/Hx8Q739/cI+/v7BP7+/gH///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP7+/gH+/v4B/f39Av39/QL7+/sEt7a2b4OAgP2DgID9gn9//4OAgP2DgID9g4CA/b28vGH8/PwD/Pz8A/39/QL9/f0C/v7+Af///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD6+voGQUBA/UFAQP0/Pj7/QUBA/UFAQP1BQED9+/v7Bf///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP39/QIXGBj9FxgY/RUWFv8XGBj9FxgY/RcYGP39/f0C////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A/f39Ag4ODv0ODg79DAwM/w4ODv0ODg79Dg4O/f39/QL///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD9/f0CDAwM/wwMDP8MDAz/DAwM/wwMDP8MDAz//f39Av///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A2traKo6OjoKPj4+DkZGRg5KSkoOUlJSDlZWVg5eXl4OYmJiDmZmZg4+Pj44vLy/9MDAw/S8vL/8yMjL9MTEx/S8vL/2Pj4+Ompqag5mZmYOXl5eDlpaWg5WVlYOTk5ODkpKSg5CQkIOOjo6DnJyccfv7+wX///8A////AP///wBBQUHvQ0ND/UdHR/1LS0v9Tk5O/1RUVP1YWFj9XFxc/WFhYf1lZWX9aGho/Wtra/1ubm79cHBw/3Jycv1wcHD9bm5u/Wtra/1nZ2f9Y2Nj/V9fX/1bW1v9VlZW/1NTU/1RVFL9VGVa/UZGRv1BQUH9ubm5VP///wD///8A/v7+ATo6Ovs4ODj9Nzc3/To6Ov07Ozv/QUFB/URERP1HR0f9S0tL/U5OTv1RUVH9U1NT/VVVVf1WVlb/WFhY/VZWVv1UVFT9UlJS/U9PT/1MTEz9SEhI/UVFRf1AQED/Pz8//Ts9PP07RD/9Ojo6/T09Pf21tbVe////AP///wD+/v4BPT099ygoKP0QEBD9EhIS/RISEv8WFhb9FxcX/RkZGf0bGxv9HBwc/R0dHf0eHh79Hx8f/R0dHf8fHx/9Hh4e/R0dHf0cHBz9Ghoa/RkZGf0XFxf9FRUV/RISEv8SEhL9EBAQ/Q4ODv0ZGRn9Pz8//be3t1v///8A////AP///wBDQ0PxKSkp/Q8PD/0RERH9ERER/xUVFf0WFhb9GBgY/RkZGf0aGhr9Gxsb/RwcHP0amX//EaR8/xWAZf4WYk7+IiYk/RoaGv0ZGRn9FxcX/RUVFf0UFBT9ERER/xEREf0PDw/9DQ0N/RoaGv0/Pz/9vLy8Vf///wD///8A////AEpKSukpKSn9Dg4O/RAQEP0QEBD/ExMT/RUVFf0WFhb9FxcX/RgYGP0ZGRn9FHhq/hGLm/8Zjo7/DZaQ/xGUkf8Rm5v/GBgY/RcX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Sv1KSkr9SUlJ/0pKSv1KSkr9SkpK/URERP1FRUX98fHxE////wD///8A////ALGxsWxKSkr9RUVF/UlJSf1MTEz/T09P/VNTU/1WVlb9WVlZ/VpaWv1UVFT9VlZW/WFhYf1iYmL/YmJi/WBgYP1eXl79XFxc/VlZWf1WVlb9U1NT/VBQUP1MTEz/SkpK/UdHR/1ERET9RERE/UVFRf329vYM////AP///wD///8A9vb2DJmZmZKPj4+ikpKSopWVlaKXl5eimpqaop2dnaKfn5+ioqKioqSkpKKlpaWip6enoqmpqaKnp6eipqamoqSkpKKioqKioKCgop2dnaKbm5uimJiYopaWlqKSkpKikJCQoo2NjaKLi4uiurq6Xv///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  NNET: {
    type: "Model Network",
    id: 169,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wASAAADEwAACRYAAA0XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFwAADhcAAA4XAAAOFgAADRMAAAgSAAAC////AP///wD///8AEQAAARMAAA8VAAApFQIEOhQRGUEUERlBFBEZQRQRGUEUERlBFBEZQRQRGkEUERpBFBEaQRQRGkEUERpBFBEaQRQRGkEUERpBFBEaQRQRGkEUERlBFBEZQRQRGUEUERlBFBEZQRQRGUEVAAA4FAAAJhMAAA0RAAAB////AP///wAUAAADEwYIHQOIy70Aner8AJ7s/wCe7P8AoPD/AKTz/wCm9/8AqPn/AKj6/wCo+v8Aqvr/AKr6/wCq+v8Aqvr/AKr6/wCq+v8AqPr/AKj6/wCn+f8Apff/AKPz/wCf7/8Anuz/AJ7s/wCc6fkEg8OsFAAAFxQAAAL///8A////ABQAAAMBl+K2AJ7s/wCe7P8AovH/AKj5/wCu//8As///ALb//wC4//8Auf//ALn//wC5//8Auf//ALn//wC5//8Auf//ALn//wC5//8Auf//ALj//wC2//8As///AK3//wCn+f8AoPD/AJ7s/wCe7P8Bld6XFAAAAv///wD///8AAo3SCQCe7P4Anuz/AKT0/wCt//8Atf//Abz//wHB//8Dvfb/BMX//wXH//8Fx///Bcb//wXG//8Fxv//Bcb//wXG//8Fxv//Bcf//wXH//8Exf//A8T//wHA//8Au///ALT//wCt//8Ao/L/AJ7s/wCe7Pb///8A////AP///wAAnuwdAJ7s/wCi8v8Arf//ALj//wHA//8HlL7/CUlc/xxHUv8gan7/DqfP/xHO//8Rzv//Ec7//xHO//8Rzv//Ec7//xHO//8Rzv//Ec7//w/O//8Nzf//Csr//wTF//8BwP//ALb//wCt//8AoPD/AJ7s/wCe7Af///8A////AACe7B0Ane7/AKr6/wC1//8Bwf//DZe//xQbHf8NDQ7/FBQU/zQ0NP8nPUL/GLja/xvX//8b1///G9f//xvX//8b1///G9f//xvX//8b1///Gtb//xfT//8T0f//Dc3//wXH//8BwP//ALT//wCn+f8Anuz/AJ7sB////wD///8AAJ7sHQCi8f8Ar///Ab3//wbD/P8lW2n/ampp/zk5Ov8TExT/CgoL/x0dHf8WbX3/It3//yLd//8i3f//It3//yLd//8i3f//It3//yDd//8f2///Hdn//xvX//8V0v//Dc3//wTF//8Au///AK3//wCf7/8AnuwH////AP///wAAnuwdAKX1/wC0//8Cwv//C8P2/1NxeP+0tLT/gICA/y8vMP8SEhP/EBAQ/xVRW/8m4v//JuL//ybi//8m4v//JuL//ybi//8m4v//JuH//yTc+f8i0u//H9r+/xvX//8T0f//Csr//wHA//8As///AKPz/wCe7gf///8A////AACe7x0Ap/n/ALj//wPF//8OzP3/SIST/9DQ0P+fn5//Ly8w/xcXGP8SExT/HYOR/ynm//8p5v//Keb//ynm//8p5v//Keb//ynl/v8gmqv/EkJK/xk1Ov8lZW//GK3L/xfT//8Nzf//A8T//wC2//8Apff/AJ/vB////wD///8AAKDwHQCr/P8Auf//Bcb//xLQ//8gt9f/h5ue/7q6uv9LS0z/Kior/z9AQf8wssL/L+j//y/o//8v6P//L+j//y/o//8v6P//KKGw/xkZGv8PDxD/ERER/zY2Nv8tPkL/FrLU/w/O//8Exf//ALj//wCn+f8AovEH////AP///wAAovEdAKz9/wm9//8mz///N9f//0Pe//9QzuT/ZKOv/2iaov9wkZb/2tjY/7PLzv9D1uj/Nur//zHp//8x6f//Men//zHn/f8yYmn/f39//0lJSv8WFhb/CgoK/x8fH/8XbH//Ec7//wXH//8Auf//AKj6/wCj8gf///8A////AACi8R0ArP3/E8D//zrT//9G2v//UOD//1nn//9f6v//Zu7//2zo9/+py8///Pv6/6PAwv9wsrr/asDK/1nm9/8/6v//MN/0/1hzd/+4uLj/iYmI/zIyM/8SEhP/EBAR/xJTYf8Rzv//Bcf//wC5//8AqPr/AKPyB////wD///8AAKLxHQCs/f8Wwv//P9X//0zb//9W4f//X+j//2Xq//9s7v//cvD//3bX4//Nzs//ycjI/3BwcP+Li4v/g6er/5DS2v+50tb/oqGi/8rKyv+oqKj/Kysr/xcXGf8YGBn/F36U/xHO//8Fxv//ALn//wCq+v8Ao/IH////AP///wAAovEdAKz9/xrD//9G1v//U93//1zi//9l6f//a+v//3Lv//948f//ebO6/4OEhP+JiYn/bm5u/4KCgv/W1tX/6+rq/9jb2/+rxMf/q7e5/7u7u/9aWlv/MzM1/yBUXv8by/H/Ec7//wXG//8Auf//AKr6/wCj8gf///8A////AACi8R0ArP3/HsT//03Y//9Z3v//Y+T//2vq//9x7P//d/D//37u/P+DnaH/uLi4/6urq/+Ghob/hoaH/66urv+crK7/mujy/531//+h6fL/pc3S/32ttP8vl6f/ItPz/xvX//8Rzv//Bcb//wC5//8Aqvr/AKPyB////wD///8AAKLxHQCs/f8jxf//VNn//2Df//9p5f//cur//3jt//9+8P//hPD9/5Gvs//Z2dn/zMzM/6Ghof+Ghob/hISF/5GprP+g9P7/o/X//6b2//+p9f//qfX//5Px//8y4P//G9f//xHO//8Fxv//ALn//wCq+v8Ao/IH////AP///wAAovEdAKz9/yjG//9b2///ZuH//3Dm//946///fu7//4Tx//+K8///lNDX/9nZ2f/f39//pqam/5GRkf+VlZb/odHX/6X1//+p9v//rPb//672//+v9v//svX//6Px//8x2///Ec7//wXG//8Auf//AKr6/wCj8gf///8A////AACi8R0ArP3/Lsj//2Hc//9u4v//duf//37s//+E7///ivL//5Dz//+h3OP/7e3s/83R0v+5u7v/qLCx/6bR1v+o9P3/q/b//672//+x9///tPf//7X2//+49f//ufT//6bv//8g0f//Bcb//wC5//8Aqvr/AKPyB////wD///8AAKLxHQCs/f8yyP//ad7//3Tj//986P//hO3//4rv//+Q8v//lvP+/8bZ2//m7O3/o+jw/6fm7f+p7fX/qvb//632//+x9///tPf//7f3//+69///uvf//732//+/9f//wPT//5Lp//8Gx///ALn//wCo+v8Ao/IH////AP///wAAovEdAKz9/zjK//9w3///e+X//4Tp//+L7v//kPD//5bz//+c3ub/+/v6/77c3/+m9v//qfb//632//+w9///s/f//7b3//+6+P//vPj//7/4///A+P//wvf//8T2///F9f//xfP//1HY//8Auf//AKj6/wCj8gf///8A////AACg8B0Aq/z/QMv//3bg//+C5v//iur//5Du//+U4Oz/lMTK/6O0tv/W1tb/qtje/6v2//+u9v//svf//7X3//+49///u/j//774///B+P//w/j//8X4///H9///yPb//8r2///L9P//t+7//wa6//8AqPn/AKLxB////wD///8AAJ/vHQCo+f9HzP//feH//4fm//+P6///lNfk/5Oam/+VlZb/lpaW/62trf+wvL3/rebt/7P2//+29///uff//7z3//+/+P//wfj//8X4///H+P//yfj//8v4///M9///zvb//8/1///P9P//TMz//wCm9/8An/AH////AP///wAAnuwdAKb1/07L//+D4f//i+f//5Tn+/+er7P/qqqr/6Kiov+goKD/oaGi/6+vr/+zxsn/tvT9/7r2//+99v//wPf//8P3///F9///yfj//8v4///N+P//z/f//9H3///S9v//0vX//9P0//+B2f//AKTz/wCe7gf///8A////AACe7B0AovH/VMr//4nh//+P5v//mt7v/7e4uf/W1tb/w8PD/66urv+rq6v/ra2t/7S4uf+67/j/vvb//8H2///E9v//x/f//8r3///M+P//zvj//9D3///S9///1Pf//9T2///W9v//1/T//4jZ//8AoPD/AJ7sB////wD///8AAJ7sHQCe7v9fyvz/keD//5Xl//+e3/H/zM3O/+fn5//W1tb/u7u7/7Ozs/+2trb/uLy9/73u+f/B9P//xPX//8f1///K9v//zfb//9D3///R9///1Pf//9b3///W9///1/b//9n2///b9f//ldv9/wCe7P8AnuwH////AP///wAAnuwdAJ7s/1/F9/+Y3v//m+T//6Dm/P/Az9P/8vLy/+Pj4/+8vL3/urq6/76+vv+/z9P/wfL+/8Xz///H9P//yvT//831///Q9v//0vb//9T3///W9///2Pb//9n2///a9v//3PX//970//+P1vn/AJ7s/wCe7Af///8A////AACe7AsAnuz/NbLw/57d+/+i4f//pub//67e7//U297/5ubm/9DQ0P/IyMj/w8zP/8Lp9f/E8v//x/L//8rz///M9P//z/T//9H1///U9v//1vb//9j2///a9v//3Pb//971///f9f//3/T+/0y78v8Anuz6AJ7sAf///wD///8A////AACe7MEAnuz/OrTw/3XN+f+B1f3/g9n//4nT8v+Vw9X/nL7M/5fG2P+S2/b/kuL//5Xj//+X5P//meT//5vl//+d5f//n+X//6Dm//+i5f//pOb//6Xl//+m4///p+L9/5vb+v9PvPL/AJ7s/wCe7KL///8A////AP///wD///8AAJ7sBQCe7MEAnuz/AJ7s/wCe7v8AovH/AKb1/wCo+f8Aq/z/AKz9/wCs/f8ArP3/AKz9/wCs/f8ArP3/AKz9/wCs/f8ArP3/AKz9/wCr/P8Ap/n/AKX1/wCi8f8Ane7/AJ7s/wCe7P4AnuyuAJ7sAf///wD///8A////AP///wD///8A////AACe7AsAnuwdAJ7sHQCe7B0Anu4dAJ/wHQCi8R0Ao/IdAKPyHQCj8h0Ao/IdAKPyHQCj8h0Ao/IdAKPyHQCj8h0Ao/IdAKLxHQCf7x0Anu4dAJ7sHQCe7B0AnuwdAJ7sCP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  RUN: {
    type: "Run",
    id: 22,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wASAAADEwAACRUAAA0WAAAOFgAADhYAAA4WAAAOFgAADhYAAA4WAAAOFgAADhYAAA4WAAAOFgAADhYAAA4WAAAOFgAADhYAAA4WAAAOFgAADhYAAA4WAAAOFgAADhYAAA4WAAAOFQAADRMAAAgSAAAC////AP///wD///8AEQAAARMAAA8UAAApEhgKQhAzE1QQMxNUEDMTVBAzE1QQMxNUEDQTVBA0E1QQNBNUEDQTVBA0E1QQNBNUEDQTVBA0E1QQNBNUEDQTVBA0E1QQNBNUEDMTVBAzE1QQMxNUEDMTVBAyE1MTEgc+EwAAJhMAAA0RAAAB////AP///wATAAADDy0SKAd4Lr0Fizb8BYw2/wWMNv8Fjjb/BY83/wWRN/8Fkjj/BZI4/wWSOP8Fkjj/BZI4/wWSOP8Fkjj/BZI4/wWSOP8Fkjj/BZI4/wWSOP8FkDf/BY83/wWNNv8FjDb/BYw2/wWKNfkIdC2sERgKHBMAAAL///8A////ABMAAAMGhjS2BYw2/wWMNv8Fjjb/BZI4/wWWOf8Fmzv/BZ07/wWfO/8FoD3/BaA9/wWgPf8FoD3/BaA9/wWgPf8FoD3/BaA9/wWgPf8FoD3/BZ87/wWdO/8Fmjr/BZY5/wWSN/8Fjjb/BYw2/wWMNv8GhDOXEwAAAv///wD///8ABYg0IQWMNv4FjDb/BZA3/wWWOf8FnTv/BaM9/wWlPv8Gpz//B6dA/winQP8Ip0D/CKdB/winQf8Ip0H/CKdB/winQf8Ip0H/CKdA/winQP8Hp0D/Bqc//wWlPv8FoT3/BZw7/wWVOP8Fjzf/BYw2/wWMNvYFjDYI////AP///wAFjDY+BYw2/wWONv8Fljn/BZ87/walPv8Ip0D/C6hC/w2pRP8PqUb/GqVM/zqmYf9cpXb/faWL/2imfv8QqUb/EKlG/xaiSP8XoUn/F6FJ/xehSP8VoUf/E6BF/xCgQ/8JokD/BZ08/wWVOP8Fjjb/BYw2/wWMNh7///8A////AAWMNj8FjDb/BZI4/wWdO/8GpT7/CadB/w2pRf8RqUj/F6dL/0KlZf98pIr/sLey/9TV1P/T09P/jqiX/xWqSv8io1D/faiM/4OokP+EqZL/haqS/4Wqkv+Fq5P/ha2T/1CqcP8FpT//BZw7/wWSN/8FjDb/BYw2H////wD///8ABYw2PwWONv8FmDn/BaM9/winQP8OqUX/E6lJ/yGmUv9upIH/s7i1/+Hi4f/x8fH/5ufm/+fn5/+SrJv/GqtO/zCfV/+0urb//f39//7//v///////v/+/97f3v+ZsaL/KahW/wenQP8FoT3/BZY5/wWNNv8FjDYf////AP///wAFjDY/BZA3/wWcO/8Gpj7/C6hD/xKpSP8gplL/cqSE/8THxf/u7u7/5ubm/93d3f/i4uL/6enp/5Wunv8frFH/NKBa/7q/vP//////////////////////rLew/0Wrav8RqUf/C6hC/wWlPv8Fmjr/BY83/wWMNh////8A////AAWNNj8Fkjj/BZ88/wenQP8OqUX/FqdL/2ukf//CxcP/7e7t/+Hh4f/g4eD/7u7u/+rr6v/Ky8r/jKqX/yGsVP81oFz/vMK+///////+//7///////7//v/U1tX/bq6F/xWoS/8NqUT/Bqc//wWdO/8FkDf/BY02H////wD///8ABY42PwWTOP8FoT3/CKdB/xCpRv8+pGP/r7Sw/+7u7v/h4eH/5OTk/+7u7v/Iycj/kKqZ/2eofv9Gp2j/JKxU/zigXf+/xMH///////////////////////////++x8H/Pqtl/w+pRf8Hp0D/BZ87/wWSOP8FjjYf////AP///wAFjjY/BZQ4/wWlP/8Kskn/HLJX/4yznP/k5eT/7Ozs/+bn5v/x8fH/wcfD/3q0k/85sGf/J65Z/yatV/8mrVf/OaFf/7zCvv/t7u3/0NLR///////+//7///////f49/+AsZH/FqdK/winQP8FoD3/BZI4/wWONh////8A////AAWONT8FlDj/BahB/wu5Tv9BuXL/u8S+//b29v/m5ub/8/Pz/9jZ2P+Mw6j/Nch1/zPKdf80y3b/Msdy/y69af8+qGb/qa+r/52zpf9+ro//2tva/////////////////7XDuv83q2H/CKdA/wWgPf8Fkjj/BY41H////wD///8ABY41PwWUOP8FqkL/C7tQ/2m7jf/b3Nv/7e7t/+jo6P/w8fD/s8W6/0fHf/80y3b/NMx3/zXNef82z3v/NtB8/03Nhv+2y77/VLh9/zisYv+atqT//v/+///////+//7/4OLh/1ivd/8Ip0H/BaA9/wWSOP8FjjUf////AP///wAFjjU/BZQ4/wWrQ/8LvVL/kb6m/+rq6v/q6ur/8PDw/+Di4f+NyKv/NMt3/zXNef82znr/NtB8/zfRff830n7/ONOA/zzUgf851oP/Ns98/3u6lf/n6Of////////////z8/P/frOR/winQf8FoD3/BZI4/wWONR////8A////AAWONT8FlDj/BqxE/wzAVP+mwrD/7u7u/+rr6v/09PT/19vZ/3jKof81znr/Ns97/zfRff830n7/ONN//znVgf851oL/OteE/zrZhf872of/idm2/+Hk4v///////v/+//X19f+RuZ//CKdB/wWgPf8Fkjj/BY41H////wD///8ABY41PwWUOP8GrkX/DMJV/6nEsv/v7+//7Ozs//b29v/a3tv/fM2l/zfQfP830n7/ONN//znUgf851oL/OteE/zrYhf872ob/PNuI/zzcif+P3Lz/7e/t///////6+vr/8/Pz/5K5oP8Ip0H/BaA9/wWSOP8FjjUf////AP///wAFjjU/BZQ4/wawRv8MxFf/mcWv/+3t7f/t7e3/9PT0/+fo5/+X0Lf/OdJ//zjUgP881YP/OteD/zrYhf872Yb/O9qH/zzcif893Yr/Pd6L/7Xh0f/19fX///////r6+v/w8PD/graV/winQf8FoD3/BZI4/wWONR////8A////AAWONT8FlDj/BrJI/wzIWf9xyZv/4uPi//T19P/09PT/+fn5/8XUy/9T1ZL/btak/8rYz/9T1pL/O9qH/zzbiP883Yr/Pd6L/z7fjP9Y4Jz/3ebg//3+/f/6+vr/+vv6//Pz8/9ktoT/CKdB/wWgPf8Fkjj/BY41H////wD///8ABY41PwWUOP8GtEn/Dcpb/0fLgv/N1dD//f39//n5+f//////6Ono/73Yyf/R29X/2t3b/17Xmf883In/Pd6L/z7fjP8+4I7/QuGR/8Dk1//y8/L//v7+//j4+P/8/Pz/7fDu/13anP8Ip0D/BaA9/wWSOP8FjjUf////AP///wAFjjY/BZQ4/wa2S/8NzV3/IM1q/7HRwP/x8vH/////////////////6erp//j5+P/k5+X/YNqc/z3fjP8+4I3/QOGP/1vioP/C5dj/7e/u//39/f/5+fn/+fn5//n6+f/i7eb/LeqG/wrCVP8FoD3/BZI4/wWONh////8A////AAWONj8Fkzj/BrhN/w3PX/8X0mf/V9KR/9ve3P///////////////////////////+jq6f9g3J3/O+CL/37it/+65db/4Onj//Pz8//+/v7/+/v7//f39//7+/v/8fPy/37svv8a7H3/DOZu/wWhPP8Fkjj/BY42H////wD///8ABY02PwWSOP8GuUz/CtJf/xTUaP8i1XH/pNjE/+jp6f//////////////////////6uzr/17env8344z/3efh//T09P/+/v7///////r6+v/4+Pj/+/v7//X29f/g7+f/Ku2H/xbue/8L7nP/BrpO/wWRN/8FjjYf////AP///wAFjDY/BZA3/we6Tf8J1GD/EtZn/xvYcP9s2qb/2+Dd///////////////////////r7uz/XuGf/zXli//j6+b//v7+//39/f/6+vr/+vr6//z8/P/29vb/5fDp/0DumP8e74P/E+95/wnwcv8Izln/BY83/wWMNh////8A////AAWMNj8Fjjb/B7pM/wjVXv8O2GX/QdqI/9Xf2f/z8/P//////////////////////+zu7f9Z45z/L+eG/+Xs6P/9/f3//f39//7+/v/6+/r/8/Tz/+Xw6f9A7pr/Ie+F/xfwf/8P8Xb/CfFx/wjOWP8Fjjb/BYw2H////wD///8ABYw2PwWMNv8Hu03/CNVf/wnaY/9/3bT/0ODW/9Pi2f/W5Nv/2OXd/9rm3v/c5+D/3Onh/0Dmkf8l6IT/5+7p//j4+P/5+fn/8/Tz/+jx6/+K78v/Ku+L/yDwhP8Z8X//EfF4/wvydP8J8W//CNJZ/wWMNv8FjDYf////AP///wAFjDY/BYw2/we4TP8I1V3/CNpj/w/cZ/8b3W7/IN5z/yTgd/8m4nr/KON7/yjkfP8n5X3/Hel8/x3qff/U7uT/5u/q/77v5f9578D/Ne6Q/xzwgP8Z8X//E/F8/w/yd/8L8nT/CfJv/wnya/8IzlX/BYw2/wWMNh////8A////AAWMNicFjDb/BqRB/wjVWP8I2V//CN1k/wjhZv8K42v/DORt/w/mcP8P53H/EOhx/xDpcv8Q6nP/EOt0/xDsdf8Q7Xb/EO52/xDvd/8Q8Hj/D/F4/w3yd/8L8nT/CfNy/wnyb/8J8mz/CfFo/wauRv8FjDb6BYw2DP///wD///8A////AAWMNsEFjDb/BqZD/wfCUf8IylX/CM1X/wjQW/8I01v/CNVf/wjWX/8I12D/CNhg/wjZYf8I2WL/CNpi/wjbY/8I3GP/CNxk/wjdZP8I3WT/CN1j/wjcYv8I21//CNpd/wjTV/8Hr0f/BYw2/wWMNqL///8A////AP///wD///8ABYw2GQWMNsEFjDb/BYw2/wWMNv8Fjjb/BZA3/wWSOP8Fkzj/BZQ4/wWUOP8FlDj/BZQ4/wWUOP8FlDj/BZQ4/wWUOP8FlDj/BZQ4/wWTOP8Fkjj/BZA3/wWONv8FjDb/BYw2/wWMNv4FjDauBYw2Df///wD///8A////AP///wD///8A////AAWMNicFjDY/BYw2PwWMNj8FjDY/BY42PwWONj8FjjY/BY43PwWONz8Fjjc/BY43PwWONz8Fjjc/BY43PwWONz8FjjY/BY42PwWNNj8FjDY/BYw2PwWMNj8FjDY+BYw2IP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  ST: {
    type: "Statistics Template",
    id: 35,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wCSjo40ko2NkpGNjZKQjIySkIuLko+Li5KPioqSjoqKko6JiZKNiYmSjYiIkoyIiJKMh4eSi4eHkouGhpKKhoaSioWFkomFhZKJhYWSiISEkoiEhJKIhISSh4ODkoeDg5KHg4OSh4ODkoeDg5KHg4NG////AP///wD///8A////AJOOjn+xrq7/z83N/8/Nzf/Ozcz/zszM/87MzP/OzMz/zszM/83MzP/Ny8v/zcvL/83Ly//My8v/zMrK/8zKyv/Mysr/zMrK/8zKyv/Lysr/y8nJ/8vJyf/Lycn/y8nJ/8rJyf/Kycn/sa6u/4eDg5////8A////AP///wD///8Ak4+Pf8jGxv/8+/v/+/j3//v49//7+Pf/+/j3//v39v/79/b/+/f2//r39v/69/X/+vb1//r29f/69vX/+vb1//r29P/69vT/+vb0//r29P/69vT/+vb0//r29P/69vT/+vb0//v6+f/Qz8//h4ODn////wD///8A////AP///wCUkI9/yMbG//z6+f/16eT/9Obi//Pl4P/y5N//8uPd//Li2//x4dr/8N/Y//De1//v3NX/79vU/+7a0//u2dL/7tjR/+3Y0P/t19D/7dfP/+3Xz//t18//7dfP/+3Xz//t2ND/+fTz/9DPz/+Hg4Of////AP///wD///8A////AJWQkH/Jxsb//Pr6//bq5v/16OP/9Ofi//Tl4f/z5N//8uPd//Hi2//x4dr/8N/Y//De1v/v3NX/79vU/+7Z0v/u2NH/7djQ/+3Xz//t1s//7dbO/+3Wzv/t1s7/7dbO/+3Wzv/59PP/0c/P/4eDg5////8A////AP///wD///8AlZGRf8nHx//8+/r/9+zp//bq5v/16eX/9ejj//Xn4v/05eH/8+Tf//Lj3f/x4tv/8eDZ//Df2P/w3tf/79zV/+/a1P/u2dL/7tnR/+3Y0P/t18//7dbO/+3Wzv/t1s7/7dbO//n08//Rz8//h4ODn////wD///8A////AP///wCWkpF/ycfH//z7+v/47uv/9+zo//br5//26ub/9unl//Xo4//15+L/9Obh//Pk3//y493/8eHb//Hg2f/w39j/8N3W/+/c1f/v29T/7tnS/+7Y0f/t19D/7dbP/+3Wzv/t1s7/+fTz/9HPz/+Ig4Of////AP///wD///8A////AJeSkn/Kx8f//Pv7//jv7P/47ur/9+3p//fs6P/26+f/9urm//bp5f/16OP/9Obi//Pl4P/y5N7/8uPd//Hh2v/x4Nn/8N/X//Dd1v/v3NX/79rT/+7Z0v/u2NH/7dfP/+3Xz//59PP/0c/P/4iEhJ////8A////AP///wD///8Al5OSf8rIyP/8+/v/+fDt//jv7P/47uv/9+3q//ft6f/37Oj/9erm//Xp5P/16OT/9efi//Tl4P/z5N//8uPd//Hi2//x4Nr/797X/+/d1v/v3NX/79rU/+7Z0v/u2NH/7tjR//n18//R0ND/iISEn////wD///8A////AP///wCYk5N/ysjI//z7+//58O3/+fDt//nv7P/47+z/+O7r/+Xa2f+5orD/uqSx/+ba1//26eX/9ejj//Xn4v/05eD/6tzX/9HCwP+2nqj/tZqm/8m3tv/l08z/7trU/+/a0//u2tP/+vXz/9HQ0P+JhYWf////AP///wD///8A////AJiUlH/LyMj//Pv7//nw7f/58O3/+fDt//nw7f/57+z/2c/P/79AxP/FOM3/qXam/+7i3v/26ub/9unl/+jb1/+peKP/xTnN/8U4zf/FOM3/xjjN/6lipP/dy8b/793W/+/c1f/69fT/0dDQ/4mFhZ////8A////AP///wD///8AmZWUf8vJyP/8+/v/+fDt//nw7f/58O3/+fDt//nw7f/z6uj/sZWr/8U3zf/GOc3/vq21//Tp5f/06OT/sZSo/8U3zf/FOM3/rVGu/6lap//FN83/xTjN/6Z0nv/r2tP/8N/Y//r29P/S0ND/ioaFn////wD///8A////AP///wCalZV/y8nJ//z7+//58O3/+fDt//nw7f/58O3/+fDt//nw7f/r4uD/rWCt/8U4zf+2S7n/4dfU/+7k4f+rYKv/xTjN/8Y4zf/PwcH/28/L/7xCwP/FOM3/t0m6/+TWz//x4dr/+vb1/9LQ0P+Khoaf////AP///wD///8A////AJqWlX/Lycn//Pv7//nw7f/58O3/+fDt//nw7f/58O3/+fDt//fu6//Rx8j/wD7G/8U4zf+pdqf/5NrY/61Zrv/FOM3/xjrN/93Sz//k2NT/t0m6/8U4zf+7RL//49bR//Lj3f/69/X/0tDQ/4uGhp////8A////AP///wD///8Am5aWf8zJyf/8+/v/+fDt//nw7f/58O3/+fDt//nw7f/47+z/+O/s//Lp5/+wk6r/xTfN/8Y5zf+6qbL/p3Sl/8U4zf/FN83/q4ql/7Seq//GOc3/xTjN/6xbq//r3dn/8+Xg//r39v/S0dH/i4eHn////wD///8A////AP///wCbl5d/zMrK//z7+//58O3/+fDt//jv7P/w5+T/1MnK/7uns/+7prP/08jJ/9/X1P+rXqz/xTjN/7ZKuv/AtLf/u0W//8U4zf/FOM3/xTjN/8U4zf/BPMj/wbC2//Pm4v/15+P/+/j3/9LR0f+Mh4ef////AP///wD///8A////AJyXl3/Mysr//Pv7//nw7f/58O3/6eDe/6pzqP/GOc3/xTjN/8U4zf/GOc7/qW2o/8C0t//APsb/xTjN/6d2pf/PxcX/q32n/65cr/+uWa//qXOm/8u+wP/y5+P/9urm//bp5f/7+Pf/09HR/4yIiJ////8A////AP///wD///8AnJiYf83Kyv/8+/v/+fDt//Tr6P+vjKr/xTnN/8U4zf+sWq3/q16r/8U4zf/FOM3/qH+k/6yOp//FN83/xjnN/7+vt//w6OX/8Ofk//Dm4//y6ef/9+3q//ft6v/37Oj/9+vn//v5+P/T0dH/jYiIn////wD///8A////AP///wCdmJh/zcrK//z7+//58O3/7eXi/7BYsf/FOM3/xTrM/9rR0P/c1NL/wj7J/8U4zf+yUrX/3dXS/61erv/FOM3/tUy5/+LZ1//58O3/+fDt//nw7f/47+z/+O/s//ju6v/37er/+/n4/9PR0f+NiYmf////AP///wD///8A////AJ2ZmX/Ny8v//Pv7//nw7f/s5OH/s1K2/8U4zf/CP8n/5NvZ/+Xc2v++RMP/xTjN/7ZMuv/p4N3/0MbH/78+xv/FOM3/qXmn//Dn5P/58O3/+fDt//nw7f/58Oz/+O/s//jv6//7+vn/09LS/46Kip////8A////AP///wD///8AnpmZf83Ly//8+/v/+fDt//Hp5v+rban/xTjN/8U3zf+vlan/spqs/8U3zf/FOM3/qmaq//Ho5f/y6ef/sJKq/8U3zf/GOc3/wbG5//bt6v/58O3/+fDt//nw7f/58O3/+fDt//z6+f/T0tL/j4qKn////wD///8A////AP///wCempl/zsvL//z7+//58O3/+O/s/8/Dxv+9QsP/xTjN/8U4zf/FOM3/xTjN/79Axf/LvsL/9+7r//nw7f/q4d//rV6u/8U4zf+1TLn/49rY//jv7P/47+z/+O/s//jv7P/47+z/+/n4/9PS0v+Pioqf////AP///wD///8A////AJ+amn/Oy8v//Pv7//nw7f/58O3/9ezq/9TJyv+qeqf/rluv/61ar/+pd6b/0cbH//Xr6f/58O3/+fDt//fu6//Sx8j/rluv/7BXsv/Dsrv/9ezp//Hp5v/u5uP/7ebj/+7m4//y8O//zs3N/46Kip////8A////AP///wD///8An5uaf87MzP/8+/v/+fDt//nw7f/58O3/+O/s//Pq6P/w5+T/8Ofk//Pq6P/47+z/+fDt//nw7f/58O3/+fDt//bt6v/w5+T/7+bj//Pq6P/w6OX/49vY/9rSz//X0M3/2dHP/+Df3v/GxMT/jYiIoP///wD///8A////AP///wCgm5t/zszM//z7+//58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/9+7r/+Pc2f+zrq3/rKel/6ulpP+sp6b/sq+u/6ilpf+Pioqg////AP///wD///8A////AKCbm3/OzMz//Pv7//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/37uv/0MrI/6SgoP/DwMH/wL6//7u4uP+sqKn/ko6N/ZGMjFv///8A////AP///wD///8AoJybf8/MzP/8+/v/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//fu6//Qysj/sa6u/+fm6P/e3d7/ysjJ/5mVlf2Tjo5m////AP///wD///8A////AP///wChnJx/z8zM//z7+//58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/9+7r/9HKyP+wrK3/3t3e/8rIyf+alpb9lJCQZ////wD///8A////AP///wD///8A////AKKcnH/Pzc3//Pv7//nx7v/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/47+z/083L/6ypqf/KyMn/m5eX/ZWRkWf///8A////AP///wD///8A////AP///wD///8Ao52df9DNzf/8/Pz//Pv7//z7+//8+/v//Pv7//z7+//8+/v//Pv7//z7+//8+/v//Pv7//z7+//8+/v//Pv7//z7+//8+/v//Pv7//z7+v/Z1tb/o5+f/5yYmP2WkpJm////AP///wD///8A////AP///wD///8A////AP///wCjnZ1/ubW1/9DNzf/Pzc3/z8zM/8/MzP/PzMz/zszM/87MzP/OzMz/zsvL/87Ly//Ny8v/zcvL/83Lyv/Nysr/zMrK/8zKyv/Mysn/y8nJ/7q3t/+XkpL9l5KSZv///wD///8A////AP///wD///8A////AP///wD///8A////AKOdnS2jnZ1/o52df6KcnH+hnJx/oZycf6Ccm3+gm5t/oJubf5+bmn+fmpp/npqZf56ZmX+dmZl/nZiYf52YmH+cl5d/nJeXf5uWln+blpZ/mZWVf5eTk03///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  TW: {
    type: "Trade Profile",
    id: 16,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AEVnghZTcoqvSGiCV////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wBHaIMzcIqf3a27xf6st7/4VXKKjE9thgf///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AR2iDW4acrfOnt8P/rbvF/sDHzP+7w8n9aYKWvVFvhx3///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AQmWBA0xth4yXqrj9p7fD/6e3w/+tu8X/wMfM/8DHzP+/xsv+h5qp41Buh0L///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AEVnghNZd5C6orPA/qe3w/+mtsL+p7fD/627xf7Ax8z/v8bL/sDHzP+/xsv+o7C6+FNwiHZObIUB////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wBGZ4MvbYid3aa2wv+nt8P/p7fD/6e3w/+nt8P/q7nE/8DHzP/Ax8z/wMfM/8DHzP/Ax8z/tr/G/VJwiK8jS2sR////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8ASGmEV4SarPOmtsL+p7fD/6a2wv6nt8P/prbC/o6isv8tU3L+mKez/7/Gy/7Ax8z/v8bL/sDHzP+/xsv+boaZ/w87X9oPO18w////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AQ2WBA01th4eVqLf9p7fD/6e3w/+nt8P/p7fD/6e3w/90jaH/F0Fk/w87X/8jSmv/r7rB/8DHzP/Ax8z/wMfM/8DHzP9uhpn/Dztf/w87X/QPO19g////AP///wD///8A////AP///wD///8A////AP///wD///8A////AEZogxFYdo+2obK//6a2wv6nt8P/prbC/qe3w/+ktMH+VHOM/xA7X/4PO1//Djpe/g87X/89X3v+vMTJ/7/Gy/7Ax8z/v8bL/m6Gmf8OOl7+Dztf/w87X/4WQWOYOlx5B////wD///8A////AP///wD///8A////AP///wBFZ4Ira4ab2aa2wv+nt8P/p7fD/6e3w/+nt8P/mau6/zVaeP8PO1//Dztf/w87X/8PO1//Dztf/w87X/9ge5D/v8bL/77Gy/+/xsv/jp+t/xQ/Yv8PO1//Dztf/1d0i/9uhpnJU3GJH////wD///8A////AP///wD///8ARWeCUoGYqvGnt8P/prbC/qe3w/+mtsL+p7fD/4SbrP4fSGn/Djpe/g87X/8OOl7+Dztf/w46Xv4PO1//EDxg/jppkP9djrj+VYew/3COpf7Ax8z/mqi0/iNLa/8OOl7+WnaN/7/Gy/6LnavqU3GIR////wD///8AQ2WBAk1th4KTp7b8p7fD/6e3w/+nt8P/p7fD/6a2wv9ng5n/Ez5h/w87X/8PO1//Dztf/w87X/8PO1//Dztf/xVCZv9IeaH/XY+5/0h4of8WQ2f/FD9i/5qptP/Ax8z/r7rB/ztdev9ado3/wMfM/8DHzP+lsrv7VnOKfVJwiAJIaoRtoLG+/qe3w/+mtsL+p7fD/6a2wv6gsb7/RmiD/g87X/8OOl7+Dztf/w46Xv4PO1//Djpe/g87X/8fTHH+U4Su/1yNt/42ZYz/EDxg/g87X/8OOl7+JUxs/7G7wv7Ax8z/vMPJ/pyrtv+/xsv+wMfM/7/Gy/64wMf+W3eNfFR0jIGnt8P/p7fD/6e3w/+nt8P/kaW0/ytScf8PO1//Dztf/w87X/8PO1//Dztf/w87X/8PO1//LVuB/1qMtv9Vh7D/I1F3/w87X/8PO1//Dztf/w87X/8PO1//QWJ+/7TAyf+0wMn/ucPK/8DHzP/Ax8z/wMfM/8DHzP9xiJuOVXWNgaa2wv6nt8P/prbC/nmRpf8YQ2X+Dztf/w46Xv4PO1//Djpe/g87X/8OOl7+ET1h/z1tlP5cjrj/SXmh/hZDaP8OOl7+Dztf/w46Xv4PO1//Djpe/hVCZv9IeaH+XY+5/0t8pP57k6b/v8bL/sDHzP+/xsv+wMfM/3KJnI5VdY2Bp7fD/6W1wf9Zd4//EDtf/w87X/8PO1//Dztf/w87X/8PO1//Dztf/xdEaP5LfKX+XI23/zdmjf8QPGD/Dztf/w87X/8PO1//Dztf/w87X/8fTHH/VIWu/1yOuP85aZD/EDxh/xdBY/+grrj/wMfM/8DHzP/Ax8z/comcjlJyi4Gbrbv+OV57/w46Xv4PO1//Djpe/g87X/8OOl7+Dztf/w46Xv4iT3X+VYaw/lWHsP8kUnj+Dztf/w46Xv4PO1//Djpe/g87X/8PO1/+LVuB/1qMtf5XibL/JlR6/g87X/8OOl7+Dztf/ypQb/60vsX/v8bL/sDHzP9yiZyOM1h2hiJKa/8PO1//Dztf/w87X/8PO1//Dztf/w87X/8PO1//MF+F/luNt/5JeqL/F0No/w87X/8PO1//Dztf/w87X/8PO1//ET1h/z1slP9cjrj/S3yk/xhFav8PO1//Dztf/w87X/8PO1//Dztf/1F0kP+cs8X/nLPF/nqTp3ISPWFUDjpe/Q87X/8OOl7+Dztf/w46Xv4PO1//ET5i/kFxmP9bjbf+OGeO/xA8YP4PO1//Djpe/g87X/8OOl7+Dztf/xdEaP5LfKT/XI64/jppkf8RPWH+Dztf/w46Xv4PO1//Djpe/g87X/8vXoX+W4y2/2GRufV7oL5dkqq9Bf///wAPO1+KDztf/w87X/8PO1//Dztf/xlGa/5Ofqf+Voix/yVTeP8PO1//Dztf/w87X/8PO1//Dztf/w87X/8hT3T+VYew/leJsv8nVXv/Dztf/w87X/8PO1//Dztf/w87X/8RPWL/QHCY/1yOuP9dj7nPcZq8KpewwwO2wckD////AA46XgQPO1+8Djpe/g87X/8kUnj+V4my/kp7o/4XRGj/Djpe/g87X/8OOl7+Dztf/w46Xv4PO1/+MV+G/luNtv5MfaX+GUZq/w46Xv4PO1//Djpe/g87X/8OOl7+GUZq/01+p/5dj7n+XI64mV2PuQr///8A////AP///wD///8A////AA87XxcPPGDhNGOK/VuMtv44aI//EDxg/w87X/8PO1//Dztf/w87X/8PO1//Ej5i/kBwmP5cjrj+O2qS/xA8Yf8PO1//Dztf/w87X/8PO1//Dztf/yRSd/9WiLH/XY+58lyPuVz///8A////AP///wD///8A////AP///wD///8A////ACVTeB1Gd587OGiPTQ87X/IOOl7+Dztf/w46Xv4PO1//Djpe/hlGa/5Of6f+V4my/yhWfP4PO1//Djpe/g87X/8OOl7+Dztf/w87X/4zYon/W423/lyOuNFcjrgp////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8ADztfWQ87X/0PO1//Dztf/w87X/8kUnj9V4iy/k1+pv8ZRmv/Dztf/w87X/8PO1//Dztf/w87X/8SP2P/Q3Ob/12Puf5cjridXI64Cv///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8ADjpejg87X/8PO1/+NGOK/VuNt/48a5P/ET1h/g87X/8OOl7+Dztf/w46Xv4PO1//G0ht/k+Bqf9cjrjyXI64X////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wAPO18FFEFlwER0nPtYibP/KVd9/w87X/8PO1//Dztf/w87X/8PO1//Dztf/ydVev9YirT/XI641FyOuCr///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wA0Y4oMSXqiIS5cg0QPO1/2Dztf/w46Xv4PO1//Djpe/g88YP83Zo3+XI64/lyOuKBcjrgK////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA87X2QPO1/+Dztf/w87X/8UQWX/Rnaf/1yOuPNcjrhh////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA87X5oOOl7+HUpv/1GDrP5cjrjVXI64LP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AET5iCSZTeb5XiLLiXI23n1yOuAv///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  UPMRD: {
    type: "UPM River Data",
    id: 58,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wAAAAACAAAAFAAAABYAAAAD////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AAAAABoGPXiVB0WKqQAAACIAAAAB////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wAAAAAEAAMGHQAAAB8AAAAKAAAAAf///wAAAAAMBCNCbgpg3vkJYef+BCxWgQAAABH///8A////AAAAAAgAAAAdAAMGIAAAAAb///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AAAAABQISI6tCU6fxgUoTHoAAgQuAAAAEQEMF0QKV7bcC2X4/wtl+P8KXMfrAxUpVQAAABIAAAAoBCJBcAhJk7sJTpzDAAAAHP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AAAAAIApNoMUNaPf/DmXq/gtSqtQFK1KOB0J/sw5n9P8OZ/j/Dmf4/w1n9/8IS5fEBCREiAlOn8kOZeX+DWf3/wtWtd0AAAAs////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wAAAAAoC1Sw1hBq+v8Qavr/EGr5/xBo8P8QaO//EGr5/xBq+v8Qavr/EGr6/xBp8f8QaO7/EGr5/xBq+v8Qavr/DV3F8QAAADb///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AAAAAAQAAADMOXMHqEm36/xJt+v8Sbfr/Em36/xJt+v8Sbfr/Em36/xJt+v8Sbfr/Em36/xJt+v8Sbfr/Em36/xJt+v8PZNf7AQsVSgAAAAL///8A////AP///wD///8A////AP///wD///8A////AAAAAAQAAAAWAAAAJgAAADAAAwY9AQwWdBBk0vgVb/n/FW/5/xVv+f8Vb/n/HXT4/0uN8/9sn+7/c6Pt/2Ga8P82gvf/Fm/5/xVv+f8Vb/n/FW/5/xJs5f4DFCaFAAMGQAAAADEAAAAnAAAAGQAAAAb///8A////AP///wD///8AAAAAGQtLkK8OVqvTD1y55hFiyfYSatr+FnDz/xhy+v8Ycvr/HXX5/3im7P/U3Of/9PT0//r6+v/6+vr/9/f3/+bn6f+zyer/R433/xhy+v8Ycvr/FnH1/xNq3f4RY8v4D1276A5XrNUMUZq9Ag0YJ////wD///8A////AP///wAAAAAZF1KQsyl++v8bdfn/G3X5/xt1+f8bdfn/G3X5/yl68P+vwdv/+fn5/+Lk5/+QpsX/b5PI/26Sx/+Nob//3N7i//v7+//j5un/c6fz/xt1+f8bdfn/G3X5/xt1+f8bdfn/HXf5/w5WpsoAAAAi////AP///wD///8A////AAAAAAcHITpoOYTm/B54+/8dePv/HXj7/x14+/8kefT/scDU//j4+P+Ho8z/Ln3u/x55+v8ugPb/N4X0/yV7+P8vfOr/fpi+//T19f/q6+z/ZKD1/x14+/8dePv/HXj7/x14+/8gefH+ByxTfgAAAAv///8A////AP///wD///8A////AAAAACMhXJvALIL7/yJ8+/8ifPv/Inz7/3SWxv/5+fn/gaXY/yN8+v9Eiu3/uMzn/+bn6P/p6ur/2N/n/4ix6v8rf/f/bo+9//j4+P/U3Of/MYT6/yJ8+/8ifPv/JHz7/xRestcAAgQwAAAAAf///wD///8A////AP///wD///8AAAAADggjPYA6iO7+JH77/yR++/8wfun/4+Xn/8vX6P8ogPn/R4bd/+Xn6v/+/v7////////////+/v7/9fX1/6bC6f8sgfb/qbXG//f39/97rPH/JH77/yR++/8lfvX/By5UkgAAABX///8A////AP///wD///8A////AAAAAA0CEB1JDkuIuCR+7/4ogvv/KIL7/1qKzP/5+fn/gK7s/y6E9//CytX//v7+////////////////////////////7u/v/12b7v9Zi83/+fn5/7fN6v8ogvv/KIL7/yZ/9P8QUpfFBBYoVgAAABEAAAAB////AAAAAAIAAAAcBihJdSx0weRIlfn/L4f7/yuF/P8rhfz/eZnD//X19f9Zm/L/TYrb//b29v///////v7+/8nS3f+9xtL//v7+///////9/f3/l7rp/z6H6P/u7u7/1N3p/y2G/P8rhfz/K4X8/yuF+f8cbcjsCDBXggAAACMAAAAEAAAAExZOg55Gj+X8VZ/8/1We/f9RnPz/Oo/8/y+J/P+Fn8L/8fHx/1OZ8/9bj9D/+vr6///////9/f3/oMLt/2OW2P/6+vr///////7+/v+kwun/Oovy/+jp6f/W3uj/M4v8/y+J/P8vifz/L4n8/y+J+/8pgOr+EE+NrgEEBxoAAAARHEx5k3aq4/lmqfz/WaL8/1mi/P9Zofz/TZr8/3eYwP/19fX/bKbu/0+N2//z8/P///////7+/v/u7+//qbrO//39/f///////Pz8/4Sx6v9Fjef/8PDw/8jX6v8zjPv/M4z7/zOM+/8zjPv/OZD8/1GZ6vwWToWjAAAAGAAAAAIAAAAZDylBa1aJu916tvv/Xqb8/12l/f9dpf3/bpjM//f39/+qyOv/PJH4/665xv/+/v7///////39/f/Cztz/+/v7//7+/v/e4+n/Rpb3/2eX0v/6+vr/nMDs/zeQ/P83kPz/N5D8/0yc+/9Bg8blDzBPeQAAAB4AAAAD////AP///wAAAAALBQ0VQStXgLFurfT+Yaj9/2Go/f9iou//0NTY/+bo6/90r/X/X5ne/83R1v/9/f3//v7+/+Lp8f/7+/v/5efp/16b4v8/lPj/u8fU/+/v8P9co/b/OpP8/zqT/P9Dl/X/JFuQvAcVIU4AAAAOAAAAAf///wD///8A////AP///wAAAAAOCCZCglqj8/5lrP3/Zaz9/2Ws/f97nML/9/f3/9Lc5/9xsPf/aqbq/4mhvv+1vcf/usLL/5Cpxf9fn+j/TZ/8/4+szf/6+vr/psXo/0ye/f9Nn/3/UKH9/0+f9/8ONlqVAAAAFf///wD///8A////AP///wD///8A////AAAAACYpZ6TLaa/9/2mv/f9or/3/aK/9/5Gz2f/w8PH/+fn5/9vh6P+VwO//bK/6/2at/P9lrfz/ZKz8/3mz8/+6zeL/+fn5//j4+P/F1+r/dbX6/2Cr/f9gqv3/X6r8/y90t98BBAc0AAAAAf///wD///8A////AP///wAAAAAHByQ+bVyj7P1ss/3/bLP9/2yz/f+Gpsj/9vb2/73N3f+Npb7/7O3t//Pz8//g5en/zt3s/8fa7P/X4Or/8fLy//X19f+jtsv/kqe9//n5+f/D0N7/Za/8/2Ou/f9irv3/WaX1/wwzV4MAAAAM////AP///wD///8A////AAAAABonY5q9dbj9/3O3/f9wtv7/b7b+/3Km2/+ms8H/dbP0/261/f9ypNf/l6q+/8/S1v/19vb/+fn5/9nc3v+is8X/eanZ/2qz/f9rrfL/lqe5/3Wu6P9nsv7/Z7L+/2ix/v9qs/3/LXCt0wAAACT///8A////AP///wD///8AAAAAGDBjkqlXgqnMYpG53GmbyO53qdn6f735/3K3/P9yuP7/cbj+/3G4/v9wt/7/cbLy/7jEz//i5+z/fbbu/262/v9ttv7/bbb+/221/v9stP3/cbb6/3Kp3PtmmsrwX4+73lSBqswwZ5m0AwwVJP///wD///8A////AP///wAAAAAEAAAAEwAAACAAAAApAAAANAMHC2lRldb4drv+/3a7/v92u/7/drv+/3W6/v91rOD/7+/v//b29v+YxPD/c7n+/3K5/v9xuf7/cbn+/3G4/v9apOn+BhQgfQAAADYAAAAqAAAAIgAAABUAAAAF////AP///wD///8A////AP///wD///8A////AP///wAAAAABAAAAMkaJxux5vv7/eL3+/3i9/v94vf7/eL3+/3ez7f+Nrs7/kbPS/4G89P91u/7/dbv+/3S7/v90u/7/dLv+/1Ca3PwDCxNIAAAAAv///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wAAAAAoQH+32nzB/v97wf7/g8T+/47G9v6HwfT+esD+/3nA/v95v/7/eb/+/3+/+P6Pw/L+hcX+/3e+/v93vv7/Ro3L8QAAADX///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AAAAAB84dKfJi8n//4zC8f5NfqrOEjBJhShVfa+NyP3/fML+/3zC/v+CxP7/LmaYwg4mO4BIdJ3Ci73p/IzK//9AgbvfAAAAK////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AAAAAEixikalEc56/ECtEcAAAACcAAAAOAwoQPVKJuduHx///gcX//1SVzekHFiNPAAAADwAAACIOJDhmPGmStDBrnr0AAAAa////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wAAAAAEAAAAGAAAABoAAAAI////AP///wAAAAAKDSc9Z3u04vh5ufD9EDNSfAAAAA////8A////AAAAAAYAAAAYAAAAGgAAAAX///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wAAAAAXIk91ji1eiqIAAAAeAAAAAf///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AAAAAAIAAAARAAAAEwAAAAP///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  UPTHR: {
    type: "UPM Threshold",
    id: 60,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wAgHx4BFBISAhAPDwIQDw8CEA8PAhAPDwIQDw8CEA8PAhAPDwIQDw8CEA8PAhAPDwIQDw8CEA8PAhAPDwIQDw8CEA8PAhAPDwIQDw8CEA8OAg4NDQILCwoCDQwMAf///wD///8A////AP///wD///8A////AP///wD///8A////AAUFBRkAAAAjAAAAIwAAACMAAAAjAAAAIwAAACMAAAAjAAAAIwAAACMAAAAjAAAAIwAAACMAAAAjAAAAIwAAACMAAAAjAAAAIwAAACMAAAAjAAAAIwAAACMCAgIZ////AP///wD///8A////AP///wD///8A////AP///wCgmJTqnJSQ/5iQjP+UjIj/koqG/5CJhf+QiYX/kImF/5CJhf+QiYX/kImF/5CJhf+QiYX/kImF/5CJhf+QiYX/kImF/5CJhf+QiYX/kImF/5CJhf+QiYX/i4SA7QAAABz///8A////AP///wD///8A////AP///wD///8A////AKWcmP////////////////////////////////////////////////////////////////////////////////////////////////////////////////+QiYX/AAAAHP///wD///8A////AP///wD///8A////AP///wD///8AqaCc///////68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7//////5CJhf8AAAAc////AP///wD///8A////AP///wD///8A////AP///wCupaD///////ry7v/68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7/+vLu//ry7v/68u7/+vLu//ry7v//////kImF/wAAABz///8A////AP///wD///8A////AP///wD///8A////ALKppP//////+vPv//rz7//8tZ///LWf//y1n//8tZ///LWf//y1n//8tZ///LWf//y1n//68+///LWf//y1n//8tZ///LWf//y1n//68+//+vPv//////+QiYX/AAAAHP///wD///8A////AP///wD///8A////AP///wD///8At62o///////68+//+vPv//y1n//68+//+vPv//rz7//68+//+vPv//rz7//68+///LWf//rz7//68+//+vPv//rz7//68+//+vPv//rz7//68+///////5CJhf8AAAAc////AP///wD///8A////AP///wD///8A////AP///wC6sKv///////rz8P/68/D//LWg//rz8P/68/D/+vPw//rz8P/68/D/+vPw//rz8P/8taD/+vPw//y1oP/8taD//LWg//y1oP/8taD/+vPw//rz8P//////kImF/wAAABz///8A////AP///wD///8A////AP///wD///8A////AL2zrv//////+vTw//r08P/8taD/+vTw//r08P/69PD/+vTw//r08P/69PD/+vTw//y1oP/69PD/+vTw//r08P/69PD/+vTw//r08P/69PD/+vTw//////+QiYX/AAAAHP///wD///8A////AP///wD///8A////AP///wD///8AwLWw///////69PH/+vTx//y1oP/69PH/+vTx//r08f/69PH/+vTx//r08f/69PH//LWg//r08f/8taD//LWg//y1oP/8taD//LWg//r08f/69PH//////5CJhf8AAAAc////AP///wD///8A////AP///wD///8A////AP///wDBtrH///////r18v/69fL//Lah//r18v/69fL/+vXy//r18v/69fL/+vXy//r18v/8tqH/+vXy//r18v/69fL/+vXy//r18v/69fL/+vXy//r18v/+/v7/kImF/wAAABz///8A////AP///wD///8A////AP///wD///8A////AMG2sf//////+/Xy//v18v/9tqH/+/Xy//v18v/79fL/+/Xy//v18v/79fL/+/Xy//22of/79fL//bah//22of/9tqH//bah//22of/79fL/+vTy//z8/P+QiYX/AAAAHP///wD///8A////AP///wD///8A////AP///wD///8Awbax///////79fP/+/Xz//22of/79fP/+/Xz//v18//79fP/+/Xz//v18//79fP//bah//v18//79fP/+/Xz//v18//79fP/+/Xz//r18v/48/H/+fn5/5CJhf8AAAAc////AP///wD///8A////AP///wD///8A////AP///wDBtrH///////v29P/79vT//bai//22ov/9tqL//bai//22ov/9tqL//bai//22ov/9tqL/+/b0//22ov/9tqL//bai//22ov/8tqH/+PPy//bx8P/39/f/kImF/wAAABz///8A////AP///wD///8A////AP///wD///8A////AMG2sf//////+/b0//v29P/79vT/+/b0//v29P/79vT/+/b0//v29P/79vT/+/b0//v29P/79vT/+/b0//v29P/79vT/+vb0//j08v/28vD/8+/u//Pz8/+QiYX/AAAAHP///wD///8A////AP///wD///8A////AP///wD///8Awbax///////79/X/+/f1//23ov/9t6L//bei//23ov/9t6L//bei//23ov/9t6L//bei//23ov/9t6L//bei//y2ov/7taH/+rSg//Pw7v/w7ev/8PDw/5CJhf8AAAAc////AP///wD///8A////AP///wD///8A////AP///wDBtrH///////v39v/79/b/+/f2//v39v/79/b/+/f2//v39v/79/b/+/f2//v39v/79/b/+/f2//v39v/69/X/+PX0//bz8f/z8O//8O3s/+zq6P/r6+v/kImF/wAAABz///8A////AP///wD///8A////AP///wD///8A////AMG2sf//////+/j2//v49v/9t6P//bej//23o//9t6P//bej//23o//9t6P//bej//23o//9t6P//Lej//u2ov/6taH/+bOf//eynv/s6un/6efl/+fn5/+QiYX/AAAAHP///wD///8A////AP///wD///8A////AP///wD///8Awbax///////7+Pf/+/j3//v49//7+Pf/+/j3//v49//7+Pf/+/j3//v49//7+Pf/+/j3//r49v/49vT/9vTy//Px8P/w7u3/7Orp/+jn5v/l4+L/4+Pj/5CJhf8AAAAc////AP///wD///8A////AP///wD///8A////AP///wDBtrH///////v5+P/7+fj//bik//24pP/9uKT//bik//24pP/9uKT//bik//24pP/8t6P/+Pb1//b08//z8fH/8O7u/+zr6v/p5+f/5ePj/+Hg3//f39//koqG/wAAABz///8A////AP///wD///8A////AP///wD///8A////AMG2sf//////+/n4//v5+P/7+fj/+/n4//v5+P/7+fj/+/n4//v5+P/7+fj/+vj3//n39v/29PP/9PLx/+/t7P/q6Of/5eTj/+Hg3//d3Nv/2tjY/9jY2P+UjIj/GxoZEv///wD///8A////AP///wD///8A////AP///wD///8Awbax///////8+vn//Pr5//24pP/9uKT//bik//24pP/9uKT//bik//24pP/8t6P/+7ai//Ty8f/x7+7/zsjF/8bBvv+/urj/t7Ox/7Ctq/+qp6X/oZ6b/5SMiO////8A////AP///wD///8A////AP///wD///8A////AP///wDBtrH///////z6+f/8+vn//Pr5//z6+f/8+vn//Pr5//z6+f/7+fn/+ff3//f19P/08vL/8e/v/+3r6//Oycb/+fn4//n5+f/19PT/5OPj/83Ly/+knJjznZeUPP///wD///8A////AP///wD///8A////AP///wD///8A////AMG2sf///////Pr6//z6+v/9uKX//bil//24pf/9uKX//bik//y3o//7tqL/+bWh//izn//t7Oz/6ejo/8/Kx//7+/v/9/f3/+bm5v/Qz8//r6ik862mozz///8A////AP///wD///8A////AP///wD///8A////AP///wD///8Awbax///////8+/r//Pv6//z7+v/8+/r//Pv6//v6+v/5+Pf/9/b1//Tz8//x8PD/7ezs/+no6P/l5eT/z8rH//f39//m5ub/0c/Q/7evq/O5sq88////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wDBtrH///////z7+//8+/v//Pv7//z7+//7+vr/+fj4//f29v/08/P/8fDw/+3s7P/p6en/5eXl/+Hh4f/NyMb/5uXm/9HQ0f++tbLzv7i1PP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AMG2sf///////Pv7//z7+//8+/v/+/v6//n5+P/39/b/9PTz//Hx8P/t7e3/6enp/+bl5f/h4eH/3d3d/8zGw//S0ND/wrq288S9uTz///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8Awbax//////////////////7+/v/8/Pz/+vr6//f39//z8/P/8PDw/+zs7P/o6Oj/5OTk/9/f3//b29v/ycK//8K5tPPEvLg8////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wDBtrHqwbax/8G2sf/BtrH/wbax/8G2sf/BtrH/wbax/8G2sf/BtrH/wbax/8G2sf/BtrH/wbax/8G2sf/BtrHvxLu3PP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  WW: {
    type: "Waste Profile",
    id: 15,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8Ad5q1A2GFoBhKbIUnfp6xEYCerwmDoK8C////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AGuNqAwrUnNJMWaQxz2Ar/VDfKHJPG6RhjdjhEdwkKMkiKOwE4qksQb///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wBwkaobLFl+cC5nlOc3fK/+RIu3/k6XwP5Wnsv+S428+UZ+ptNFdpeXRXGQW42ptjSNp7Idj6auCv///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wBriqEDaYmjMjZkipgsa5/4O3yt/myfxP6Wvdb+i7nX/nuz1/5lpdH+XqDP/mGgyf5fnMH8W5O02l+Qq6Nmj6VuhaKvRn2Xoyl8lJ0OkqSlAf///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AaYeeDzpjhFQtYIm/M3Om+zp1o/5wk63+ucPL//X19v7v9Pj+0ePx/rLS6f6bw+H/fKi//pCdi/+HoZ/+f6q1/3Cpw/pTjrThQXigskJ0loNjiJ1afpuoL6C3vwj///8A////AP///wD///8A////AP///wD///8A////AGiDmSM8ao97Lmub2Sxsn/xMgqv+hZ+1/re7wP7S0tP/+Pj4/v7+/v7+/v7+/v7+/vX5/P+kubr+uItB/7iNSv6gjl7/jK2r/mKo0f9QmMn+UpjG/FCSu+ZakLKZm7bDHv///wD///8A////AP///wD///8A////AGt+jQlQaXxEP2+WozJypOsydqr+XIiq/5qruP7AwMP+yMjK/tjY2f/5+fn+/v7+/v7+/v7+/v7+/////6q8uv6ugj3/xY09/rWHPf+tuaP+lsfi/6fL5P6IvN7+ba/Y/naw0cGmwc0p////AP///wD///8A////AIaaqAFvgI4YPlhqbEd3mco+f7D1O3+y/nKXtP6nsrv+wsLE/snJy/7Pz9H+3t7e/vr6+v7+/v7+/v7+/v7+/v7+/v7+q727/r6QQf7FjT3+s4c+/qy6p/683e7+9Pj7/uPv9v7U5vP+wdfkwLrN1Cj///8A////AP///wB4h5IBJyssFD1PWWhZj7LlUJXF/FiVwv+Kp77+tLnA/8TExv/Lysz+0NDS/tbW2P7j4+T/+/v7//7+/v7///////////////+su7v+uotG/8WNQv7BlEr/qLep/r7e7/////////////7+/v7s7e+7ydXZJ////wD///8A////AHWBigcLCggeOk1VfHWz1P53qsv+oLPB/ry/w/7Gxsj+zMzN/9LS0/7Y2Nn+3d3f/ufn6P76+vr+/v7+/v7+/v7+/v7+/v7+/rTN2f7Zx6z/w49N/samd/+jtKv+wN/v/v7+/v7+/v7+/v7+/u/v8LrM1dgm////AP///wD///8AeICHAg8ODBM9TVV0krXJ/7C5wf/BwcT/x8fJ/s3Nz//T09T/2dja/9zc3f7g4OH/6ejp//X09P/5+fn+/v7+////////////utTi/uHWxP/JnGH/5+HX/5+wq/7C3/D////////////+/v7+8PDwuMzU1iX///8A////AP///wD///8AgoWICXp6fG28vL/+xMTG/srKzP7Pz9D+09PU/tXU1f7V1NX+1NPT/tHMyf7Mw73+6ujn/u7u7/74+Pj+/f39/v7+/v6vx9T+vLKi/ruXZv7a1Mn+mayq/sXg8P7+/v7+/v7+/v7+/v7v7++0ztPUJP///wD///8A////AP///wCcm5oIvb2+bsjIyv/Ozs//0NDR/9DQ0P7Ozs//zc3O/8fFxf67rqT+lHFU/5loR/+8ppv/49/e/u7u7v/4+Pj//v7+/8ze6P6quLr/nKGb/p2elv+Sq7L+y+Tx/////////////v7+/u/v8LPS1NMk////AP///wD///8A////AKWfmgrNzc1yzs3O/s3Nzv7Ly8z+yMjK/sbFxf67tK//pYx5/pNeNf6sZTH+rWcz/qdwTP69ppv+4d3c/u3t7f74+Pj+/f39/v/////6/f3+5/P4/9Xo8f7n8/j+/v7+/v7+/v7+/v7+9PT0r9jX1CL///8A////AP///wD///8AppuSC8XExnTHx8j/xcXG/sPDxP63tbP+qpqP/pdvUf+iYjH+sGgy/rFoM/6xaTP/rmk1/ql0UP6/qJ3/39va/uzs7f/u49v+79/R//Xq4v769fH//fv7/v7+/v/+/v7+/v7+/vz8/f709PWu2tbSIv///wD///8A////AP///wComIsMurq7d8DAwf65uLj+qKCc/puAbf6ZZT7+rGYz/rFpM/6yaTT+smo0/rJrNP6zazX+r2o3/qp2Uv7Aqp7+3tva/tCym/7RqIb+166Q/uTGs/7r1sj++fPv/v7+/v78/P3+8/P0/uPi46yyqqcnoZCHBf///wD///8A////AKiTgwytra14raqp/peIfv6UblP+omU6/q9pNP6yajT/sms0/rNsNf6zbDX+tG02/7RtNv60bjb+sWw4/qt3VP7Aq6H/w6GI/tO6p//Kmnr+4b+p/9mwlf727Ob//f39/vX19f7o6On+sK+x1m9eWZ17UDtRysG9Bf///wD///8AoodwFIF2bYmGb179lWRB/qhmNv6xajT+sms0/rNsNf+zbTb+tG02/rRuNv61bzf/tW83/rZwNv62cDf/sm44/qt4VP+qf2P+zLeq/8Sgi/7ix7f/27ae/vjy7v/29vb+6ejo/sHAwf57bmr9e1M/1LCRf0nNxL8E////AKSBZhRrUDeNelM14J1iNf6taDT+sms0/rNsNf6zbTb+tG02/7VuNv61bzb+tnA3/rdwN/63cTf+t3I3/rdyN/64cjf+tHE5/qVtRP60m47/v6OU/tjEuf/au6b+8+zp/ujo6f7BwMH+g3Zy/oFYQs2xkHxSybuyCv///wCrhmkBeVQ1MY9YLuSnZDH+sWk0/rJrNP6zbDX+tG01/rVuNv61bzb+tnA2/rdxN/63cjf+uHM3/rh0N/64dDj+uXU4/rl1OP65dTj+tnQ6/qd0T/6kgnH+wJ+L/seolv7h2tf+wsLD/oN3c/6AWEPFrot1Sce1qQj///8A////AP///wCoelUOr2w2dbNrNfazazX+tGw2/rRuNv61bzb+tnA3/rdxN/+4cjf+uHM3/rl1OP66djn+unY6/rp3O/67dzz+u3g8/rt4PP67eDz+uXY9/6FvS/6xnJL/0sa//sG9uv6Cd3L9f1lEwK2HcD/HsKAF////AP///wD///8A////AP///wCxek4St3I6fbVvN/S0bjb/tW82/7ZwN/63cjf/uXM4/7p1OP+6djr+u3c7/7x4PP+9eT7/vXo//r57QP++e0D/vnxB/758QP6+e0H/u3pA/6N1U/+kmZX+fnNu+n5aRbWpgmgxxKiTAf///wD///8A////AP///wD///8A////AP///wCydkUXuXU9ibdyOfG3cTf+t3I3/rl0OP66djn/u3c7/rx5Pf69ej7+vntA/r98Qf7AfUL+wH5D/sF/Q/7Bf0P+wX9D/sF+Q//AfkP+u3tC/pZoRPGAXEWqpHpfJ////wD///8A////AP///wD///8A////AP///wD///8A////AP///wC2d0Mgu3hClrl1O/G5dDj+unY6/rx4PP69ej7+vntA/r99Qv7AfkP+wYBE/sKARf7CgUf+w4JI/sOCSf7Dgkj+w4JI/sKBR/zBgUXbunxEja17VR7///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wC5eUUovnxGobx5PvK8eT3+vno//798Qf7Af0P+wYBF/sOCSP7Eg0r+xIRN/sWGUP7Gh1L+xodT/saHU/7GhlLxxIVPt8CEUFG9hFME////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wC9fUowwYFNq799Q/W/fUL/wX9E/sKBR/7EhEv+xYZQ/8aIVP7HiVj+yItb/smMXf7KjF78yYxd1MSIWYbBhlYg////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wDAgU42xYdUtcKBR/nDgkj+xYVO/saIVP7Iilr/yY1f/sqPY/7MkWf+zJJo7MyRZ6nGil5QvYVXCf///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wDEhVM6yI1bwsWGUPzHiFf+yYxe/suPZP7Nkmn+zpVt+8+WcM3KkGR1xYpdJb+FVgP///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AMGBTAHPmXE8zpZr0sqNYP7MkWf+zpVt/tCYc+zQmXWgzJJoRMSIVw7///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AMeLWwLUo4BB0Zx34c+Wb/vRmnXSzpVuZ8iMXB3HiVgD////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AMmNXwTYqo1F1KB/kc+XcC/Ii1oK////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AMmNXwPJjF4KyItcAf///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  ENV: {
    type: "Engineering validation",
    id: 52,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wCSjo40ko2NkpGNjZKQjIySkIuLko+Li5KPioqSjoqKko6JiZKNiYmSjYiIkoyIiJKMh4eSi4eHkouGhpKKhoaSioWFkomFhZKJhYWSiISEkoiEhJKIhISSh4ODkoeDg5KHg4OSh4ODkoeDg5KHg4NG////AP///wD///8A////AJOOjn+xrq7/z83N/8/Nzf/Ozcz/zszM/87MzP/OzMz/zszM/83MzP/Ny8v/zcvL/83Ly//My8v/zMrK/8zKyv/Mysr/zMrK/8zKyv/Lysr/y8nJ/8vJyf/Lycn/y8nJ/8rJyf/Kycn/sa6u/4eDg5////8A////AP///wD///8Ak4+Pf8jGxv/8+/v/+/j3//v49//7+Pf/+/j3//v39v/79/b/+/f2//r39v/69/X/+vb1//r29f/69vX/+vb1//r29P/69vT/+vb0//r29P/69vT/+vb0//r29P/69vT/+vb0//v6+f/Qz8//h4ODn////wD///8A////AP///wCUkI9/yMbG//z6+f/16eT/9Obi//Pl4P/y5N//8uPd//Li2//o2NX/m5HB/2Nes/92b7b/xbbJ/+7a0//u2dL/7tjR/+3Y0P/t19D/7dfP/+3Xz//t18//7dfP/+3Xz//t2ND/+fTz/9DPz/+Hg4Of////AP///wD///8A////AJWQkH/Jxsb//Pr6//bq5v/16OP/9Ofi//Tl4f/z5N//8uPd/5mRwf8+Pbb/VFTW/0hIx/9WUq//69fS/+7Z0v/u2NH/7djQ/+3Xz//t1s//7dbO/+3Wzv/t1s7/7dbO/+3Wzv/59PP/0c/P/4eDg5////8A////AP///wD///8AlZGRf8nHx//8+/r/9+zp//bq5v/16eX/9ejj/+/h3v+gl8f/QkG2/2Nj5f90dPH/bW3u/z8/vf+bkL//7NrT/+/a1P/u2dL/7tnR/+3Y0P/t18//7dbO/+3Wzv/t1s7/7dbO//n08//Rz8//h4ODn////wD///8A////AP///wCWkpF/ycfH//z7+v/47uv/9+zo//br5//26ub/qaHM/0RCtv9aWt3/c3Pw/3d37/90dPL/Xl7i/09LrP/Pwc3/8N3W/+/c1f/v29T/7tnS/+7Y0f/t19D/7dbP/+3Wzv/t1s7/+fTz/9HPz/+Ig4Of////AP///wD///8A////AJeSkn/Kx8f//Pv7//jv7P/47ur/8Obl/6Wezf9FRbr/WVnc/3Bv6/91de3/d3fv/3V18P9vb/H/RUXD/394uv/t3Nf/8N/X//Dd1v/v3NX/79rT/+7Z0v/u2NH/7dfP/+3Xz//59PP/0c/P/4iEhJ////8A////AP///wD///8Al5OSf8rIyP/8+/v/+fDt//bt6/+ZlM3/Q0O6/1hY2v9sbOf/cXHo/3V17f93d/D/dXXw/3Fx7/9dXeP/PDux/8W5zP/x4Nr/8N/Y//De1//v3NX/79rU/+7Z0v/u2NH/7tjR//n18//R0ND/iISEn////wD///8A////AP///wCYk5N/ysjI//z7+//y6en/npnP/0JCvf9WVtn/Z2fg/2xs4v9xcOr/bGzt/2tr7f9ycvH/cXHu/2lo6/9LS87/Z2O2/+TW1//x4tv/8eDa//Df2P/w3db/79vV/+/a0//u2tP/+vXz/9HQ0P+JhYWf////AP///wD///8A////AJiUlH/LyMj//Pv7/7Gr2P9BQbz/V1fZ/2Fh2v9mZtv/bGzl/2Ji5P9CQb//OTi0/2Fh5f9wcPD/aWnp/2Ji6f9AP7f/npbG//Di3f/y493/8eHb//Hg2f/w3tf/793W/+/c1f/69fT/0dDQ/4mFhZ////8A////AP///wD///8AmZWUf8vJyP/8+/v/a2jF/0pKz/9bW9P/Xl7U/2Zm3/9fX+L/QkK//4uHyf+Lhsn/RETG/2tr7v9qauj/YmLm/1FR1v9LSbL/2c7X//Pl4P/y5N//8uLc//Hh2v/w39j/8N/Y//r29P/S0ND/ioaFn////wD///8A////AP///wCalZV/y8nJ//z7+/9kYsT/TU3R/1tb0/9gYNr/WVnb/0JCvf+Wkc3/9+7s/+nh5v9NTLj/V1fe/2lp6v9gYOP/Wlri/0JCxv91cb3/7eDf//Tm4f/z5eD/8uPe//Hi2//x4dr/+vb1/9LQ0P+Khoaf////AP///wD///8A////AJqWlX/Lycn//Pv7/5+a1P88PL//UVHV/09P0/9AP77/lpLP/+/m6P/58O3/9+7s/52Yz/8/P77/aGju/2Bg4/9YWN3/VFTe/z49s/+wqM7/9Ofj//Xn4v/z5eD/8uTe//Lj3f/69/X/0tDQ/4uGhp////8A////AP///wD///8Am5aWf8zJyf/8+/v/8enp/6qk1f9nZcP/bWrF/7+52v/58O3/+fDt//nw7f/58O3/59/l/2lnv/9PT9T/YWHm/1dX2/9RUdr/TEzU/0tJs//Pxdj/9unl//Xo4//05uH/8+Xg//r39v/S0dH/i4eHn////wD///8A////AP///wCbl5d/zMrK//z7+//58O3/+fDt//Dn5//z6un/+fDt//nw7f/58O3/+fDt//nw7f/58O3/xr/a/zo6uf9aWuH/V1fc/01N1f9OTtn/Pz/D/3Ftvf/w5eT/9urm//Xo5P/15+P/+/j3/9LR0f+Mh4ef////AP///wD///8A////AJyXl3/Mysr//Pv7//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/47+z/h4PJ/0NDxP9aWuL/Tk7V/0hI0f9NTdn/PTy5/5eSyf/x5uT/9urm//bp5f/7+Pf/09HR/4yIiJ////8A////AP///wD///8AnJiYf83Kyv/8+/v/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/c1OL/W1m8/01N1P9SUtz/RkbP/0ZG0f9KStX/RUS0/8C41v/37Oj/9+vn//v5+P/T0dH/jYiIn////wD///8A////AP///wCdmJh/zcrK//z7+//58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//jv7P/DvNr/Q0K6/09P2f9JSdL/QkLM/0lJ1P9FRcz/UE62/+HY4P/37er/+/n4/9PR0f+NiYmf////AP///wD///8A////AJ2ZmX/Ny8v//Pv7//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f+Sjcz/PT2//09P2v9ERM7/QkLM/0xM2P8/P8P/d3TA/+jg4//7+vn/09LS/46Kip////8A////AP///wD///8AnpmZf83Ly//8+/v/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt/+be5f90ccT/QkLH/0xM2P9ERM3/RETO/05O2f88O7j/op3P//z6+f/T0tL/j4qKn////wD///8A////AP///wCempl/zsvL//z7+//58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt/97W4v9aWL3/Q0PN/0pK1v9CQsz/RkbR/0dH0P9fXbr/+/n4/9PS0v+Pioqf////AP///wD///8A////AJ+amn/Oy8v//Pv7//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt/8S92v9IR7n/SUnS/0lJ1f9LS9X/RkbM/2Vju//y8O//zs3N/46Kip////8A////AP///wD///8An5uaf87MzP/8+/v/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+O/s/7q01/9GRbj/Q0PM/0NDyv9FRLL/qaTE/+Df3v/GxMT/jYiIoP///wD///8A////AP///wCgm5t/zszM//z7+//58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/9Ovp/7KtzP9kYqz/ZGGp/46Jpf+ppKX/sq+u/6ilpf+Pioqg////AP///wD///8A////AKCbm3/OzMz//Pv7//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/37uv/0MrI/6SgoP/DwMH/wL6//7u4uP+sqKn/ko6N/ZGMjFv///8A////AP///wD///8AoJybf8/MzP/8+/v/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//fu6//Qysj/sa6u/+fm6P/e3d7/ysjJ/5mVlf2Tjo5m////AP///wD///8A////AP///wChnJx/z8zM//z7+//58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/9+7r/9HKyP+wrK3/3t3e/8rIyf+alpb9lJCQZ////wD///8A////AP///wD///8A////AKKcnH/Pzc3//Pv7//nx7v/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/58O3/+fDt//nw7f/47+z/083L/6ypqf/KyMn/m5eX/ZWRkWf///8A////AP///wD///8A////AP///wD///8Ao52df9DNzf/8/Pz//Pv7//z7+//8+/v//Pv7//z7+//8+/v//Pv7//z7+//8+/v//Pv7//z7+//8+/v//Pv7//z7+//8+/v//Pv7//z7+v/Z1tb/o5+f/5yYmP2WkpJm////AP///wD///8A////AP///wD///8A////AP///wCjnZ1/ubW1/9DNzf/Pzc3/z8zM/8/MzP/PzMz/zszM/87MzP/OzMz/zsvL/87Ly//Ny8v/zcvL/83Lyv/Nysr/zMrK/8zKyv/Mysn/y8nJ/7q3t/+XkpL9l5KSZv///wD///8A////AP///wD///8A////AP///wD///8A////AKOdnS2jnZ1/o52df6KcnH+hnJx/oZycf6Ccm3+gm5t/oJubf5+bmn+fmpp/npqZf56ZmX+dmZl/nZiYf52YmH+cl5d/nJeXf5uWln+blpZ/mZWVf5eTk03///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  SIM: {
    type: "DWF",
    id: 23,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AHKxawt7tHWjfLR1o3ezcAv///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wBzsWwLh7uBw3ORb/9zkW//iLuCw3m0cgv///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8Ac7FrC4e7gcN0lHD/IEob/yBKG/90lHD/iLuCw3i0cQv///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AHKxawuHu4HDept2/yRTHv8kUx7/JFMe/yRTHv96m3b/iLuCw3i0cQv///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wBxsWoLh7uBw4Kmff8pXyL/KV8i/ylfIv8pXyL/KV8i/ylfIv+Cpn3/h7uBw3e0cAv///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AcbBqC4e7gcOKsIX/L2wn/y9sJ/8vbCf/L2wn/y9sJ/8vbCf/L2wn/y9sJ/+KsIX/h7uBw3ezcAv///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AHCwaQuHu4HDkLmM/zN3K/8zdyv/M3cr/zN3K/8zdyv/M3cr/zN3K/8zdyv/M3cr/zN3K/+QuYz/h7uBw3azbwv///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wBwsGgLh7uBw5W+kP82fS3/Nn0t/zZ9Lf82fS3/Nn0t/zZ9Lf82fS3/Nn0t/zZ9Lf82fS3/Nn0t/zZ9Lf+VvpD/h7uBw3azbgv///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8Ab7BoC4e7gcOVwJD/NIQs/zeBLv84gS//MI4o/xy/Gv8O3hj/Cesf/wzkGv8Xyhj/K58k/zeBLv84gS//OIEv/ziBL/+VwJD/h7uBw3Wzbgv///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AG+vZwuHu4HDlsGR/ziBL/8VzxL/HMEX/x67Gv8S9kP/Vv+k/2b/sP9Y/5//RP+T/y//hf8V/Vf/FdEY/zSHK/84gS//OIEv/ziBL/+WwZH/h7uBw3WybQv///8A////AP///wD///8A////AP///wD///8A////AP///wBur2YLh7uBw5bBkf84gS//OIIv/xPUF/8i/XT/Ov6H/4T/vv+B/73/Yv+u/0L/kv9C/5b/QP+P/yn/av8n/4H/D90Y/zWFLP84gi//OIIv/ziBL/+WwZH/h7uBw3SybQv///8A////AP///wD///8A////AP///wD///8Aba9lC4e7gcOWwZD/OIIv/ziCL/84gi//E9QZ/1v/qf9y/6L/dP+8/wj1O/8Xyxb/IbUd/xvCGf8H7iX/OP+Q/yn/Zf8m/nz/GsUY/ziCL/84gi//OIIv/ziCL/+WwZH/h7uBw3OybAv///8A////AP///wD///8A////AG+waAuGu4DDlcCQ/ziCL/84gi//OIIv/ziCL/8T1Bn/Sf+f/17/nv86/5L/F8sU/zeCLv84gi//OIIv/zOIK/8P3Rb/QP+Z/zL/ef8J9Tn/Mogq/ziCL/84gi//OIIv/ziCL/+VwJD/hruAw3Wybgv///8A////AP///wBysWsLh7uBw5jCk/84gi//OIIv/ziCL/84gi//OIIv/xzBGP8L5iX/C+Ym/wvmJv8N4w7/LZEm/ziCL/84gi//OIIv/y+SJ/8V+lH/RP+D/yv/ef8lrB//OIIv/ziCL/84gi//OIIv/ziCL/+XwZL/h7uBw3i0cQv///8A////AHu0daObw5b/OIIv/ziCL/84gi//OIIv/ziCL/84gi//N4Eu/zZ/Lf82fy3/Nn8t/zZ/Lf84gS//OIIv/ziCL/84gi//OIIv/wroHf9h/6j/Qf+S/xzAGv84gi//OIIv/ziCL/84gi//OIIv/ziCL/+bw5b/frZ3o////wD///8AfLR1o5vDlv84gi//OIIv/ziCL/84gi//OIIv/ziCL/84gi//OIIv/ziBL/84gi//OIIv/ziCL/84gi//OIIv/ziCL/84gi//Cugf/3T/tv9Q/5v/HMAa/ziCL/84gi//OIIv/ziCL/84gi//OIIv/5vDlv9+tnij////AP///wB3s3ALiLuBw5jCk/84gi//OIIv/ziCL/84gi//OIIv/zaCLf8pmyL/FdAX/yijIf84gi//OIIv/ziCL/84gi//OIIv/y+QKP8a+Vb/gP+1/0X/kv8lrR//OIIv/ziCL/84gi//OIIv/ziBL/+WwJH/iLuBw322dgv///8A////AP///wB3s3ALhrqAw5O9jv83gC7/OIIv/ziCL/84gi//GMkX/wL7T/8k/4H/CO0i/zCNKP84gi//OIIv/ziCL/80hyv/ENwX/2v/tv+E/7z/FfdL/zGIKf84gi//OIIv/ziCL/82fi7/kryN/4a6gMN8tnUL////AP///wD///8A////AP///wBzsmwLh7uBw463if80eiz/N4Au/ziCL/8noiH/Af1P/xn/Vv8j/3n/BfQx/xnIGP8irx3/HMAa/wjtIf9I/5r/dP+k/1f/pf8YyRj/OIEv/ziCL/82fS3/NHgr/463iv+Hu4HDebVyC////wD///8A////AP///wD///8A////AP///wB0sm0Lh7uBw4uzh/8xcSn/MnQq/zN4K/8Ywhf/Cf1g/xn/W/8e/2X/H/90/xX/af8g/3T/M/99/0L/e/9J/53/Dd8b/zJ/Kf8zdyv/MXIp/zFxKf+Ls4f/h7uBw3q1cwv///8A////AP///wD///8A////AP///wD///8A////AP///wB1sm0Lh7uBw4iwhP8vbCf/L2wn/y1sJf8XoRb/A9Y0/xjgYv8f42H/HOVY/x3lXv8i4mn/Dd1R/w+3FP8qcSP/L2wn/y9sJ/8vbCf/iLCE/4e7gcN6tXML////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wB1s24Lh7uBw4asgf8tZyX/LWcl/y1nJf8lcR//FJ4U/wm3Fv8FwR3/B7sZ/xCmFP8gfxv/K2cl/y1nJf8tZyX/LWcl/4asgf+Hu4HDe7Z0C////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wB2s24Lh7uBw4Oof/8qYiT/KmIk/ypiJP8qYiT/KmIk/ypiJP8qYiT/KmIk/ypiJP8qYiT/KmIk/ypiJP+DqH//h7uBw3u2dAv///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wB2s28Lh7uBw4CkfP8oXSL/KF0i/yhdIv8oXSL/KF0i/yhdIv8oXSL/KF0i/yhdIv8oXSL/gKR8/4e7gcN8tnUL////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wB3s3ALh7uBw36gef8mWSD/Jlgg/yZYIP8mWCD/Jlgg/yZYIP8mWCD/Jlkg/36gef+Hu4HDfLZ1C////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wB3s3ALiLuCw3udd/8kVB7/JFQe/yRUHv8kVB7/JFQe/yRUHv97nXf/iLuBw3y2dgv///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wB4tHELiLuBw3iadP8iTx3/Ik8d/yJPHf8iUB3/eJp0/4i7gsN9tnYL////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wB4tHELiLuCw3aXcv8gSxv/IEsb/3aXcv+Iu4LDfbd2C////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wB5tHILiLuCw3eWc/93lnP/iLuCw363dwv///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wB4tHELfrZ3o362eKN9tnYL////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  RAR: {
    type: "Risk Analysis Run",
    id: 198,
    icon: "data:image/png;base64,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"
  },
  IC1D: {
    type: "Initial Conditions 1D",
    id: 202,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wAxMTE2NjY2qjU1Nek1NTX9NTU1/zU1Nf81NTX/NTU1/zU1Nf81NTX/NTU1/zU1Nf81NTX/NTU1/zU1Nf81NTX/NTU1/zU1Nf81NTX/NTU1/zU1Nf81NTX/NTU1/TQ0NOkzMzOqLy8vNv///wD///8A////AP///wD///8ANzc3aj4+PvxFRUX/RkZG30pKSsBMTE2/TU1Nv01NTb9NTU2/TU1Nv01NTb9NTU2/TU1Nv01NTb9NTU2/TU1Nv01NTb9NTU2/TU1Nv01NTb9NTU2/TU1Nv01NTb9LS0zASkpK301NTf87Ozv8MDAxav///wD///8A////ADg4ODZFRUX8Pz9A5zg4OEP///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8APDw8Q01NTec8PDz8MTExNv///wD///8ARUVFq0JCQv82NjZC////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8APDw8Qk5OTv82Njar////AP///wBJSUnpOTk53v///wD///8A////AP///wD///8A////AKsRoImrEKCOqxGgaqwRoUauEaMW////AP///wD///8A////AP///wD///8AE3UTIRNzEzwTdBMmEnISBf///wD///8A////AP///wD///8AS0tM3jg4OOn///8A////AEpKSv45OTrA////AP///wD///8A////AP///wD///8AqxGg+asRoP+rEaD/qxGg/6gSnrwTdBMeE3MTNhN0E2cTcxOZE3MTwBNzE/sTcxP/E3MT/xNzE/8TcxPjE3MTjhN1EyoVgBUH////AP///wBNTU7AOjo7/v///wD///8AS0tL/zs7PL////8A////AP///wD///8A////AKwRoRKrEaD/qxGg/6sRoP+rEaD/mxuR+BNzE/QTcxP/E3MT/xNzE/8TcxP/E3MT/xNzE/8TcxP/E3MT/xNzE/8TcxP/E3MT8RJzEm0UexQL////AFBQUL88PDz/////AP///wBMTEz/PT09v////wD///8A////AP///wD///8AqxGgVqsRoP+rEaD/qxGg/6sRoP+eGJT/E3MT/xNzE/8TcxP/E3MT/xNzE/8TcxP/E3MT/xNzE/8TcxP/E3MT/xNzE/8TcxP/E3MT6BNzE14UfRQDUVFRvz09Pv////8A////AE1NTf8+Pj+/////AP///wD///8A////AP///wCrEaCbyDHA/8kywf/CK7n/uiOx/5olkv8TcxP/E3MT/xNzE/8TcxP/E3MT/xZ/Fv8ZjBn/GIYY/xR2FP8TcxP/E3MT/xNzE/8TcxP+E3MTvRN0EyhRUVG/Pj4//////wD///8ATU1O/z8/QL////8A////AP///wD///8A////AKsRoM7sVOf/8Fbq/+5V6f/tU+f/wk29/xV8Ff8clxz/I68j/yjCKP8u2S7/MOEw/zHjMf8x4jH/Ltcu/yW0Jf8Xghf/E3MT/xNzE/8TcxPzE3QTXVJSUr9AQED/////AP///wBOTk//QUFBv////wD///8A////AP///wD///8AqxKh4/Ra7//0Wu//9Frv//Ra7/+yfq7/NfA1/zXwNf818DX/NfA1/zXwNf818DX/NfA1/zXwNf818DX/NfA1/zPrM/8goyD/E3QT/xNzE/8TcxN+UVJSwUFBQf////8A////AE9PT/9BQUK/sBGlGa8RpB7HE7oC////AP///wDAKrfp9Frv//Ra7//0Wu//9Frv/4+mjP818DX/NfA1/zXwNf818DX/NfA1/zXwNf818DX/NfA1/zXwNf818DX/NfA1/zTtNP8enx7/E3QT/xJzErdQVFDHQkJC/////wD///8AT09Q/0JCQ7+rEaCZqxGgt6sRoFSrEaASsxGoDsozwev0Wu//9Frv//Ra7//0Wu//b8Fu/zXwNf818DX/NfA1/zXwNf8y6DL9NO805jXwNec18DX/NfA1/zXwNf818DX/NO80/y7ZLv8Yhxj/E3MT4k9VT8tDQ0P/////AP///wBQUFD/Q0NEv6sRoOarEaD9qxGg5KsRoIusEaFT1j/P8PRa7//0Wu//9Frv//Ra7/9Y1Ff/NfA1/zXwNf818DX/KcUp/x6dHv0w4DBYNfA1VjXwNbk18DX6NfA1/zXwNf818DX/M+kz/yKrIv8TcxP3T1VQzUNDRP////8A////AFBQUP9DQ0S/qxGg+6sRoP+rEaD/qxGg86sRoNveRtf79Frv//Ra7//0Wu//6Ffj/1HWUP818DX/NfA1/zXwNf8muSb/FXoV/hN1ExxA/0ACNfA1PDXxNck18DX/NfA1/zXwNf807zT/KMIo/xR5FP1PVk/ORERE/////wD///8AUFBQ/0NDRL+rEaD+qxGg/6sRoP+rEaD/qxGg/udN4P70Wu//9Frv//Ra7//dXdj/TthN/zXwNf818DX/NfA1/yrHKv8WgBb/E3MTVv///wA3/DcKNfA1jTXwNf818DX/NfA1/zXwNf8t0i3/GYkZ/U9WT85ERET/////AP///wBQUFD/Q0NEv886yP7YQND/th2s/60Tov+sE6H/7lTo//Ra7//0Wu//9Frv/8lwxfFI3kf7NfA1/zXwNf818DX/LdIt/xiFGP8TcxOp////ABN1Ewsw3jB7NO409zXwNf818DX/NfA1/y/aL/8bkRv7UFZQzUNDRP////8A////AFBQUP9DQ0O/4Urb+vNZ7v/nT+H/xy+//7sksf/vVen/9Frv//Ra7//0Wu//wH691ULlQfQ18DX/NfA1/zXwNf8x5TH/Go0a/xNzE+ITcxNaE3MThiCkINIx4jH+NfA1/zXwNf818DX/MeMx/x6dHutPVVDMQ0ND/////wD///8AT09P/0JCQr/tVOjx9Frv//Ra7//tVOf/3ETW//FX7P/0Wu//9Frv//Ra7/+8hbmoO+s76TXwNf818DX/NfA1/zTuNP8clRz/E3MT/RNzE/8TcxP/HJQc/zDdMP818DX/NfA1/zXwNf8y5TL/Iakhv1BUUMdCQkP/////AP///wBOTk//QUFBv/Ra79n0Wu//9Frv//Ra7//zWe7/81nu//Ra7//0Wu//9Frv/8x5yHg27zbdNfA1/zXwNf818DX/NfA1/yGoIf8TdBP/E3MT/xNzE/8emx7/MeIx/zXwNf818DX/NfA1/zDfMP8ltyWCUlNSwUFBQv////8A////AE5OTv9AQEC//l75FfRa74j0Wu/29Frv//Ra7//0Wu//9Frv//Ra7//vVur851bhWDXwNco18DX/NfA1/zXwNf818DX/J74n/xR2FP8TcxP/FXoV/ya6Jv807jT/NfA1/zXwNf818DX/MN4w5ia5JlFSUlK/QEBA/////wD///8ATU1N/z4+P7////8A/2H/BfVa8Fn0Wu/h9Frv/vRa7//0Wu//9Frv/+9V6fPnT+FQNfA1nTXwNf818DX/NfA1/zXwNf8rziv/FoEW/x6bHv8qyir/NO00/zXwNf818DX/NfA1/zXwNf018DWZNfQ1BlFRUr8/Pz//////AP///wBMTEz/PT0+v////wD///8A/2H/BPVa8Gn0Wu/r9Frv//Ra7//0Wu//7lTp1+VM3zs18DVxNfA1/zXwNf818DX/NfA1/zPsM/807zT/NfA1/zXwNf818DX/NfA1/zXwNf818DX+NfA1yzXyNT////8AUVFRvz09Pv////8A////AEtLTP88PDy/////AP///wD///8A+1z1E/Ra77D0Wu/89Frv//Ra7//yWO287VPoJzXyNUs18DX/NfA1/zXwNf818DX/NfA1/zXwNf818DX/NfA1/zXwNf818DX/NfA1/zXwNdA18TVF////AP///wBQUFC/PDw8/////wD///8AS0tL/jo6OsD///8A////AP///wD///8A9FrvSvRa76j1WvDE9Frv3/Va8Jv9XfgSNvg2EzXwNf818DX/NfA1/zXwNf818DX/NfA1/zXwNf818DX/NfA1/zXwNd018TWhNfI1OP///wD///8A////AE1NTcA7Ozv+////AP///wBMTEzpODg43v///wD///8A////AP///wD/Yf8G91vyFvxd9x35W/Ml+FvzG/lb9AP///8ANfA15jXwNf818DX/NfA1/zXwNf818TXONfA1oTXwNX418jVJNfA1JTf6NxP///8A////AP///wD///8ASEhI3jk5Oen///8A////AEdHR6tCQkL/MjIyQv///wD///8A////AP///wD///8A////AP///wD///8A////AP///wA18TWQNfA1pjXxNWc29DYtNfA1CP///wD///8A////AP///wD///8A////AP///wD///8A////ADc3N0JGRkf/OTk6q////wD///8AOzs7Nk9PT/w2NjfnMTExQ////wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wA0NDRDPz9A5z8/P/w0NDQ2////AP///wD///8APT0+aU5OTvxAQEH/NDQ14DU1NcA2Nja/NjY2vzY2Nr82Nja/NjY2vzY2Nr82Nja/NjY2vzY2Nr82Nja/NjY2vzY2Nr82Nja/NjY2vzY2Nr82Nja/NjY2vzY2Nr82NjbANjY24EBAQf9FRUX8ODg4af///wD///8A////AP///wD///8AOzs7NkVFRapJSUnoSEhI/UdHR/9HR0f/R0dH/0dHR/9HR0f/R0dH/0dHR/9HR0f/R0dH/0dHR/9HR0f/R0dH/0dHR/9HR0f/R0dH/0dHR/9HR0f/R0dH/0dHR/1HR0foREREqjk5OTb///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  IC2D: {
    type: "Initial Conditions 2D",
    id: 167,
    icon: "data:image/png;base64,Qk02EAAAAAAAADYAAAAoAAAAIAAAACAAAAABACAAAAAAAAAQAAAAAAAAAAAAAAAAAAAAAAAA////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wAwMDA2NTU1qjQ0NOk0NDT9NDQ0/zQ0NP80NDT/NDQ0/zQ0NP80NDT/NDQ0/zQ0NP80NDT/NDQ0/zQ0NP80NDT/NDQ0/zQ0NP80NDT/NDQ0/zQ0NP80NDT/NDQ0/TMzM+kyMjKqLi4uNv///wD///8A////AP///wD///8ANjY2aj09PfxERET/RUVF30lJScBLS0y/TExMv0xMTL9MTEy/TExMv0xMTL9MTEy/TExMv0xMTL9MTEy/TExMv0xMTL9MTEy/TExMv0xMTL9MTEy/TExMv0xMTL9KSkvASUlJ30xMTP86Ojr8Ly8wav///wD///8A////ADc3NzZERET8Pj4/5zc3N0P///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8AOzs7Q0xMTOc7Ozv8MDAwNv///wD///8AREREq0FBQf84NzVEhWszDIJoMQ6EajMLgmkyBn9lLAN9YykCe2MpAXRjJgH///8A////AP///wD///8ATmkkAUlsJQFDbiYCPnAmAjlyJgI1dCcCMHYoAv///wD///8A////AP///wD///8AOzs7Qk1NTf81NTWr////AP///wBISEjpODg43pd6PRSbhlhNkHlHXZeBUk+UfEk9h2wuLoRoKSWFbS8ehHEyGIF1NhJ9ezsLd4A+CWx/Og1dfTQVUHsuHkR5KCY6eCQqNXkjKzJ7Jio1gi4iO4o4EzaLNQYuiS4B////AP///wD///8ASkpL3jc3N+n///8A////AElJSf45ODnAo4ZKKJ2MaJx7ZDLTgWs8yH9nNLp3XCCremAlmYRtNoaNekV2lYZVZZ2TZlOdnG9KjJZkVm2MT25OgzyFNngpmidx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F/4chRz+Kb4p/jLoMv407zT+NO80/kDpQOxI30hmUVtRwkBAQf////8A////AE1NTf9BQT/AvpAvTtWbH/fXmhn91JgZ/sGKFv6UaxH+bU8M/XFRDf6idRL+1pkZ/uOjG/7jpBz/wrEg/m3WLP447TT+MuYy/iayJv0diB3+Howe/iawJv4v2i/9M+0z/jTvNP417zX8Xu1exFvjW0VRVVHBPz8//////wD///8ATExM/z8+PsC/lTg/4a072eKjHPziohr+2ZwZ/riEFf6QaBD+j2YQ/riEFf7bnRr+46Mb/uKjG/7BsR/+bNcs/jftM/4z6zP+LdMt/inBKf4szCz+MOAw/jPsM/407zT+Nu82/EXwReNw7XCEYeNhIVBSUcA+Pj7/////AP///wBLS0v/PTw9v8GbSiLnwGuU5Kot6eKjHPzhoRr92JsZ/sePF/3FjRf+15oZ/eGiGv7iohr93aUb/a65Iv1c3S7+NO4z/TPuM/4y6jL9Mugy/jPrM/0z7jP+M+4z/TfvN/lG70bfXOtcmF7iXjtL3UsJUFBQvzw8Pf////8A////AEpKS/87Ozu/vZdECtu6dUHmul2h5a004uOkIPjiohv94KAa/uCgGv7iohv+46Mb/eOlIPfTsCztj8sx8kjnMv007zT+NO80/jTvNP417zX9Oe85+D/wP+9G70bhTO5MxlzpXIta4Fo+SNhIDkLbQgFPT0+/Ozs7/////wD///8ASkpK/jk5OcC9kTUBx6FPD9u3akDitVSG4as4tuawPcznsDzY56433uauN97lsDrX3rNAu77AR6N03ETKP+059ULxQuxL8UvgUPBP00bsQsNG6kGxVOxSm2HsYXxa5lpWUd5RK0bYRgxA10AB////AExMTMA6Ojr+////AP///wBLS0vpNzc33v///wDFlzUBy6BDC9KlRCTYqUU/4rhcVuO5Wmnft1Fz27lRc9a9V2fFvlJHob9BPHHSO3JY3zucY+NLi3DnXXZ152RfXuJLR03gPzhO40gsUuNQHUrgSg5C20IE////AP///wD///8AR0dH3jg4OOn///8A////AEZGRqtBQUH/MTExQv///wD///8A0J4yAtSiNwfZqEAN1qo/FM+tPBfFsTwXurY9E6y4OgmYujIIhMAxGnnINCZ2zzwgdNVEGG7aRxBe2z8IT948BEfiPwND40IC////AP///wD///8A////ADY2NkJFRUb/ODg5q////wD///8AOjo6Nk5OTvw1NTbnMDAwQ////wD///8A////AP///wDWqDQBzaw0AcCxMgH///8A////AP///wCQwTMBhcc0AnzONgFz1DgB////AP///wD///8A////AP///wD///8A////AP///wAzMzNDPj4/5z4+PvwzMzM2////AP///wD///8APDw9aU1NTfw/P0D/MzM04DQ0NMA1NTW/NTU1vzU1Nb81NTW/NTU1vzU1Nb81NTW/NTU1vzU1Nb81NTW/NTU1vzU1Nb81NTW/NTU1vzU1Nb81NTW/NTU1vzU1Nb81NTXANTU14D8/QP9ERET8Nzc3af///wD///8A////AP///wD///8AOjo6NkRERKpISEjoR0dH/UZGRv9GRkb/RkZG/0ZGRv9GRkb/RkZG/0ZGRv9GRkb/RkZG/0ZGRv9GRkb/RkZG/0ZGRv9GRkb/RkZG/0ZGRv9GRkb/RkZG/0ZGRv1GRkboQ0NDqjg4ODb///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AP///wD///8A////AA=="
  },
  "SIM-FAIL": {
    type: "Sim type",
    id: null,
    icon: ""
  },
  Unknown: {
    type: "Unknown",
    id: -5,
    icon: ""
  }
};

// src/InfoLiteTransportableVersions.json
var InfoLiteTransportableVersions_default = {
  "{C1AA7612-F6DA-46ce-BE75-7AEF7640965C}": 5,
  "{DAAC6FA7-0D69-4F31-8DEB-3B02D9032435}": 5.5,
  "{F00FFC6D-96DB-41D1-B0FB-78AD415DEADB}": 6,
  "{CCCA38C1-5615-4883-86FD-422D0C06E2F0}": 6.5,
  "{FDE1819E-9138-4F62-9CB6-94C136EC2EF3}": 7,
  "{DE74A25A-747E-4CFA-A625-1DB600EBFFD7}": 7.5,
  "{AA2B3387-2625-422D-A6EF-6CAFA2DADCC7}": 8,
  "{CBCFB6A9-1827-424B-BB09-F56BE669A1CB}": 8.5,
  "{E0BDC1BA-874D-46D5-B10E-984F66C89C61}": 9,
  "{B9AC6189-9316-4C73-9F6C-ED6E788E2888}": 9.5
};

// src/InfoLiteTransportable.ts
async function parseEntry(entry) {
  return new Promise(async (resolve, reject) => {
    let fileName = entry.filename;
    let id = null;
    let type = "";
    let icon = "";
    let isDeleted = false;
    if (fileName.match(/RootObjects\.dat/i)) {
      id = 0;
      type = "Root";
      icon = "";
    } else if (fileName.match(/Globals\.dat/i)) {
      id = -1;
      type = "DB:Globals";
      icon = "";
    } else {
      let parts = fileName.match(
        /^(?<typeID>[A-Z]+?)(?<deleted>XXX)?(?<cumulativeID>\d+)\.DAT$/
      );
      isDeleted = parts?.groups?.deleted === "XXX";
      let cumulativeID = parseInt(parts?.groups?.cumulativeID || "0", 10);
      let typeData = InfoLiteEntryTypes_default[parts?.groups?.typeID || "Unknown"];
      if (!typeData)
        throw new Error(`Unknown typeID: ${parts?.groups?.typeID}`);
      if (typeData.id != null) {
        id = typeData.id + cumulativeID * 256;
      } else {
        id = null;
      }
      type = typeData.type;
      icon = typeData.icon;
    }
    let writer = new TextWriter();
    if (!entry?.getData) {
      reject(new Error("Entry or entry.getData is undefined."));
      return;
    }
    let text = await entry.getData(writer).catch((error) => {
      reject(new Error("Error getting data from entry: " + error));
    });
    if (!text) {
      reject(
        new Error(
          "Error getting data from entry: No text returned from entry " + entry.filename
        )
      );
      return;
    }
    let data = text.split(/\r?\n/).reduce((acc, line) => {
      let match = line.match(
        /^\s*(?<name>[^,]+),\s*(?<valid>[01]),\s*(?<value>.*)$/
      );
      if (match) {
        if (match.groups?.valid === "1") {
          acc[match.groups?.name] = match.groups?.value;
        }
      }
      return acc;
    }, {});
    resolve({
      id,
      type,
      icon,
      isDeleted,
      zipEntry: entry,
      data
    });
  });
}
var InfoLiteTransportable = class _InfoLiteTransportable {
  /**
   * Creates a new instance of the InfoLiteTransportable class.
   * @param data - The constructor arguments.
   */
  constructor(data) {
    __publicField(this, "file");
    __publicField(this, "zip");
    __publicField(this, "root", null);
    __publicField(this, "deleted", []);
    __publicField(this, "globals");
    console.log({ constructorData: data });
    this.file = data.file;
    this.zip = data.zip;
    let globals = data.parsedEntries.find((e2) => e2.type == "DB:Globals");
    let root = data.parsedEntries.find((e2) => e2.type == "Root");
    let rest = data.parsedEntries.filter(
      (e2) => !["Root", "DB:Globals"].includes(e2.type)
    );
    this.globals = globals?.data;
    if (!root) throw new Error("No Root entry found.");
    this.root = {
      name: "Root",
      type: "Root",
      path: ">Root",
      depth: 0,
      data: root,
      children: []
    };
    let entryStore = {
      "0": this.root
    };
    rest.forEach((entry) => {
      let id = entry.id;
      if (id != null) {
        entryStore[id.toString()] = {
          name: entry.data.Name,
          type: entry.type,
          data: entry,
          children: []
        };
      }
    });
    rest.forEach((entry) => {
      if (entry.id == null) return;
      const parentMain = entryStore[entry.data["#Parent"]];
      const entryMain = entryStore[entry.id?.toString()];
      if (entryMain.data.isDeleted) {
        this.deleted.push(entryMain);
      } else {
        parentMain.children.push(entryMain);
      }
    });
    let setDepthAndPath = (node, path = "", depth = 0) => {
      node.depth = depth;
      node.path = `${path}>[${node.type}] ${node.name}`;
      node.children.forEach((child) => {
        setDepthAndPath(child, node.path, depth + 1);
      });
    };
    setDepthAndPath(this.root);
  }
  /**
   * Tests if a file is a valid InfoLite transportable database.
   * @param file - The file to test.
   * @returns - A boolean indicating whether the file is a valid InfoLite transportable database.
   */
  static TestFile(file) {
    return file.name.endsWith(".icmt");
  }
  /**
   * Creates a new instance of the InfoLiteTransportable class from an ArrayBuffer.
   * @param buffer - The ArrayBuffer to create the instance from.
   * @returns - A Promise that resolves to the new instance of the InfoLiteTransportable class.
   */
  static async CreateFromArrayBuffer(buffer) {
    const blob = new Blob([buffer]);
    return await _InfoLiteTransportable.CreateFromFile(blob, true);
  }
  /**
   * Creates a new instance of the InfoLiteTransportable class from a icmt file.
   * @param file - The file to create the instance from.
   * @param force - A boolean indicating whether to force the creation of the instance even if the file does not have a valid InfoLite transportable database extension.
   * @returns - A Promise that resolves to the new instance of the InfoLiteTransportable class.
   */
  static async CreateFromFile(file, force) {
    if (!file) {
      throw new Error("File is required.");
    }
    if (file.size === 0) {
      throw new Error("File is empty.");
    }
    if (!_InfoLiteTransportable.TestFile(file) && !force) {
      throw new Error("Invalid file type. Expected .icmt file.");
    }
    let oZIP = new ZipReader(new BlobReader(file));
    let entries = await oZIP.getEntries();
    if (entries.length === 0) {
      throw new Error(
        "No entries found in the transportable database. Invalid."
      );
    }
    let parsedEntries = (await Promise.all(
      entries.map(async (entry) => {
        if (!entry.directory && entry.filename.match(
          /^(?:(?:\w+?\d+\.DAT)|(?:RootObjects\.DAT)|(?:Globals\.DAT))$/i
        )) {
          return await parseEntry(entry);
        } else {
          return null;
        }
      })
    )).filter((entry) => entry != null);
    return new _InfoLiteTransportable({
      file,
      zip: { file: oZIP, entries },
      parsedEntries
    });
  }
  /**
   * Converts the transportable database to a DSL string that can be used to validate the database.
   * @returns - A DSL string that describes the structure of the transportable database.
   */
  toValidationDSL() {
    let dsl = ["Root"];
    let recurse = (obj, depth) => {
      depth++;
      obj.children.forEach((child) => {
        dsl.push("|  ".repeat(depth) + `|- 1# [${child.type}] /${child.name}/`);
        recurse(child, depth);
      });
    };
    recurse(this.root, 0);
    return dsl.join("\r\n");
  }
  /**
   * Returns the version of the transportable database.
   * @returns - The version of the transportable database. E.G. 9.5.1234
   */
  getVersion() {
    return `${InfoLiteTransportableVersions_default[this.globals?.VersionGUID]}.${this.globals?.SubVersion}`;
  }
  /**
   * Validates the transportable database against a DSL schema.
   * @param dslSchema - A DSL string that describes the expected structure of the transportable database.
   * @param vars - A map of variables that can be used in the DSL string.
   * @returns - An array of error messages.
   */
  validate(dslSchema, vars) {
    let dsl = this.parseDSL(dslSchema, vars);
    if (this.root == null) throw new Error("Root is null");
    let cloner = (entry) => {
      return {
        ...entry,
        children: entry.children.map(cloner),
        errors: []
      };
    };
    let tree = cloner(this.root);
    let errors = [];
    const recurse = (schemaNode, actualNode) => {
      if (schemaNode.type !== "ANY" && actualNode.type !== schemaNode.type) {
        let error = {
          expected: schemaNode,
          actual: actualNode,
          error: {
            id: 1,
            message: `Expected type '${schemaNode.type}', got '${actualNode.type}'.`,
            type: "actual:self-expected:self"
          }
        };
        errors.push(error);
        actualNode.errors.push(error);
        return;
      }
      const matchedChildren = /* @__PURE__ */ new Set();
      for (const expectedChild of schemaNode.children) {
        const matches = actualNode.children.filter((child) => {
          const isTypeMatch = expectedChild.type === "ANY" || child.type === expectedChild.type;
          const isNameMatch = expectedChild.name === null || expectedChild.name.test(child.name);
          return isTypeMatch && isNameMatch;
        });
        matches.forEach((match) => matchedChildren.add(match));
        if (matches.length < expectedChild.min) {
          let error = {
            expected: expectedChild,
            actual: actualNode,
            error: {
              id: 2,
              message: `Expected at least ${expectedChild.min} child(ren) of type [${expectedChild.type}] matching ${expectedChild.name}, found ${matches.length}.`,
              type: "actual:parent-expected:child"
            }
          };
          errors.push(error);
          actualNode.errors.push(error);
        }
        if (matches.length > expectedChild.max) {
          let error = {
            expected: expectedChild,
            actual: actualNode,
            error: {
              id: 3,
              message: `Expected at most ${expectedChild.max} child(ren) of type [${expectedChild.type}] matching ${expectedChild.name}, found ${matches.length}.`,
              type: "actual:parent-expected:child"
            }
          };
          errors.push(error);
          actualNode.errors.push(error);
        }
        matches.forEach((match) => {
          recurse(expectedChild, match);
        });
      }
      const unexpectedChildren = actualNode.children.filter(
        (child) => !matchedChildren.has(child)
      );
      unexpectedChildren.forEach((child) => {
        let error = {
          expected: schemaNode,
          actual: child,
          error: {
            id: 4,
            message: `Unexpected child "[${child.type}] ${child.name}" of parent "[${actualNode.type}] ${actualNode.name}".`,
            type: "actual:child-expected:parent"
          }
        };
        errors.push(error);
        child.errors.push(error);
      });
    };
    recurse(dsl, tree);
    return errors.length > 0 ? { type: "error", tree, errors } : { type: "success", tree };
  }
  /**
   * Preprocesses the DSL string by replacing variables with their corresponding regular expressions.
   * @param dsl - The DSL string to be preprocessed.
   * @param vars - The variables to be replaced.
   * @returns - The preprocessed DSL string.
   */
  preprocessVars(dsl, vars) {
    let processed = dsl;
    for (const [key, regex] of Object.entries(vars)) {
      const pattern = regex.toString().slice(1, -1);
      processed = processed.replace(new RegExp(`\\$${key}`, "g"), pattern);
    }
    return processed;
  }
  /**
   * Parses the DSL string and returns a validation tree.
   * @param dsl - The DSL string to be parsed.
   * @param vars - The variables to be used in the DSL string.
   * @returns - The validation tree.
   */
  parseDSL(dsl, vars = {}) {
    dsl = this.preprocessVars(dsl.trim(), vars);
    const lines = dsl.split("\n").map((line) => line.trim()).filter(Boolean);
    const root = {
      type: "Root",
      name: /Root/,
      min: 1,
      max: 1,
      children: []
    };
    const tokens = lines.slice(1).map((line, index) => this.parseDSLLine(line, index + 2));
    const stack = [{ node: root, depth: -1 }];
    for (const token of tokens) {
      while (stack.length && stack[stack.length - 1].depth >= token.depth) {
        stack.pop();
      }
      const parent = stack[stack.length - 1].node;
      parent.children.push(token.node);
      stack.push({ node: token.node, depth: token.depth });
    }
    return root;
  }
  /**
   * Parses a single line of the DSL string and returns a validation token.
   * @param line - The line of the DSL string to be parsed.
   * @param lineNumber - The line number of the DSL string.
   * @returns - The validation token.
   */
  parseDSLLine(line, lineNumber) {
    const depth = (line.match(/\|/g) || []).length;
    let clean = line.match(/\|- (.*)/)?.[1].trim();
    if (clean == null) throw Error(`DSL line has incorrect syntax "${line}"`);
    switch (clean) {
      case "Root":
        return {
          depth,
          node: {
            type: "Root",
            name: null,
            min: 1,
            max: 1,
            children: [],
            lineNumber
          }
        };
      case "*":
        return {
          depth,
          node: {
            type: "ANY",
            name: /.*/,
            min: 0,
            max: Infinity,
            children: [],
            lineNumber
          }
        };
    }
    const data = clean.match(
      /\s*(?<count>\d+\+?|\d+-\d+)?#\s+\[(?<type>[^\]]*)]\s+(?<pattern>\/(?:\\\/|[^\/])*\/i?)/
    );
    if (data == null) throw new Error(`Invalid line: '${clean}'`);
    const { count, type, pattern } = data.groups;
    const regexParts = pattern.match(
      /\/(?<regexPattern>(?:\\\/|[^\/])*)\/(?<regexFlags>[iuA]*)/
      //A is a custom flag for unanchoring the regex. All regexes will be anchored by default.
    );
    if (regexParts == null)
      throw new Error(
        `Invalid pattern found in line "${lineNumber}" of Validation DSL: '${pattern}'`
      );
    let { regexPattern, regexFlags } = regexParts.groups;
    if (!regexFlags.includes("A")) {
      regexPattern = `^${regexPattern}$`;
    } else {
      regexFlags = regexFlags.replace("A", "");
    }
    const regexNameMatcher = new RegExp(regexPattern, regexFlags);
    let min = 0;
    let max = 0;
    if (count) {
      if (count.includes("-")) {
        const parts = count.split("-");
        min = parseInt(parts[0], 10);
        max = parseInt(parts[1], 10);
      } else if (count.includes("+")) {
        const parts = count.split("+");
        min = parseInt(parts[0], 10);
        max = Infinity;
      } else {
        min = parseInt(count, 10);
        max = min;
      }
    } else {
      min = 1;
      max = 1;
    }
    return {
      depth,
      node: {
        type,
        min,
        max,
        name: regexNameMatcher,
        children: [],
        lineNumber
      }
    };
  }
};
function validationResultsToString(result) {
  let lines = [];
  let recurse = (node, depth, hasInheritedError = false) => {
    const indent = "|  ".repeat(depth);
    const label = `[${node.type}] ${node.name}`;
    const isDirectError = node.errors.length > 0;
    const status = isDirectError ? "\u26D4" : hasInheritedError ? "\u{1F7E4}" : "\u2705";
    if (node.errors.length == 1) {
      lines.push(
        `${status} ${indent}|- ${label} ::: ${node.errors[0].error.message}`
      );
    } else if (node.errors.length > 1) {
      for (const error of node.errors) {
        lines.push(`${status} ${indent}|  |- ${error.error.message}`);
      }
    }
    node.children.forEach((child) => {
      recurse(child, depth + 1, isDirectError || hasInheritedError);
    });
  };
  recurse(result.tree, 0);
  return lines.join("\n");
}
export {
  InfoLiteTransportable as default,
  validationResultsToString
};
//# sourceMappingURL=InfoLiteTransportable.js.map
