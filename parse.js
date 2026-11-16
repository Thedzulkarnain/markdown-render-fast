// A fast, dependency-free reimplementation of marked 18.1.3's default
// (GFM) rendering: parse(markdown) returns exactly the HTML marked
// produces, byte for byte. Two passes: an index-based block scanner with
// sticky regexes (no repeated slicing of the remaining input), then a
// hand-rolled inline scanner that renders straight to a string instead
// of building token objects. No state is kept between calls.

'use strict';

// ---------------------------------------------------------------- helpers

const ESC_MAP = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };
const escTest = /[&<>"']/;
const escReplace = /[&<>"']/g;
const escTestNoEncode = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/;
const escReplaceNoEncode = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

// Escape HTML. encode=true escapes every & < > " '; encode=false leaves
// a & alone when it already starts a valid character/entity reference.
function esc(s, encode) {
  if (encode) {
    if (escTest.test(s)) return s.replace(escReplace, (c) => ESC_MAP[c]);
  } else if (escTestNoEncode.test(s)) {
    return s.replace(escReplaceNoEncode, (c) => ESC_MAP[c]);
  }
  return s;
}

const numRefTest = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const numRefOrAmp = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

// Decode numeric character references in a text run (&#38; -> &amp; etc.).
// A bare & that is not a valid reference becomes &amp; only when the run
// also holds a numeric reference; otherwise the renderer escapes it.
function unescNumeric(s) {
  if (!numRefTest.test(s)) return s;
  return s.replace(numRefOrAmp, (m, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const code = dec === undefined ? parseInt(hex, 16) : parseInt(dec, 10);
    if (code === 0 || code > 0x10FFFF || (code >= 0xD800 && code <= 0xDFFF)) return '\uFFFD';
    if (code === 38) return '&amp;';
    return String.fromCodePoint(code);
  });
}

const percentDecode = /%25/g;
function cleanUrl(s) {
  // encodeURI leaves a plain ASCII URL untouched (it only encodes %, space,
  // controls, non-ASCII and <>"{}|\^`[]); skip the encode when none occur.
  if (!/[%<>"{}|\\^`\[\]\s\x00-\x1F\x7F-\uFFFF]/.test(s)) return s;
  try {
    return encodeURI(s).replace(percentDecode, '%');
  } catch {
    return null;
  }
}

// Split a table row on unescaped pipes, honouring a column limit.
function splitCells(s, max) {
  const t = s.replace(/\|/g, (ch, off, str) => {
    let odd = false;
    for (let p = off - 1; p >= 0 && str[p] === '\\'; p--) odd = !odd;
    return odd ? '|' : ' |';
  });
  const cells = t.split(/ \|/);
  if (cells[0].trim()) { /* keep */ } else cells.shift();
  if (cells.length > 0 && !cells[cells.length - 1].trim()) cells.pop();
  if (max) {
    if (cells.length > max) cells.splice(max);
    else while (cells.length < max) cells.push('');
  }
  for (let i = 0; i < cells.length; i++) cells[i] = cells[i].trim().replace(/\\\|/g, '|');
  return cells;
}

// Strip trailing copies of ch from a string.
function rtrimCh(s, ch) {
  let n = s.length;
  while (n > 0 && s.charCodeAt(n - 1) === ch) n--;
  return s.slice(0, n);
}

// Drop trailing blank lines when more than one trails.
function stripBlankTail(s) {
  const lines = s.split('\n');
  let t = lines.length - 1;
  while (t >= 0 && /^[ \t]*$/.test(lines[t])) t--;
  return lines.length - t <= 2 ? s : lines.slice(0, t + 1).join('\n');
}

// Normalize a link reference label: collapse whitespace, fold case.
function normLabel(s) {
  return s.trim().replace(/\s+/g, ' ').toLowerCase().toUpperCase().toLowerCase();
}

// Find the index of the closing bracket that matches the opens in s,
// -1 when balanced/absent, -2 when an open is left unclosed.
function findClose(s, pair) {
  if (s.indexOf(pair[0]) === -1 && s.indexOf(pair[1]) === -1) return -1;
  let depth = 0;
  for (let i = 0; i < s.length; i++) {
    if (s[i] === '\\') { i++; continue; }
    if (s[i] === pair[0]) depth++;
    else if (s[i] === pair[1]) {
      depth--;
      if (depth < 0) return i;
    }
  }
  return depth > 0 ? -2 : -1;
}

// Expand tabs to spaces, starting at column col.
function expandTabs(s, col = 0) {
  let out = '';
  let t = col;
  for (const ch of s) {
    if (ch === '\t') {
      const w = 4 - (t % 4);
      out += ' '.repeat(w);
      t += w;
    } else {
      out += ch;
      t++;
    }
  }
  return out;
}

const punctTestRe = /^((?![*_])[\s\p{P}\p{S}])/u;
function isPunctChar(c) {
  return c !== '' && punctTestRe.test(c);
}
const alphaNumRe = /[\p{L}\p{N}]/u;

// ------------------------------------------------------- regex composition

// marked builds its big patterns by splicing small ones together; the
// caret rule drops a ^ that a spliced-in pattern carries at its start
// (a ^ that is not inside a character class).
const caretRe = /(^|[^\[])\^/g;
function compose(tpl, reps) {
  let t = typeof tpl === 'string' ? tpl : tpl.source;
  for (const [pat, rep] of reps) {
    let o = typeof rep === 'string' ? rep : rep.source;
    o = o.replace(caretRe, '$1');
    t = t.replace(pat, () => o);
  }
  return t;
}
function rx(src, flags) {
  return new RegExp(src, flags);
}
// Strip ^ anchors (outside character classes) so a pattern can run
// sticky at any index; ^ inside [...] is left alone.
function stripCaret(src) {
  return src.replace(caretRe, '$1');
}

const BLOCK_TAGS = 'address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul';
const BULLET = ' {0,3}(?:[*+-]|\\d{1,9}[.)])';
const HR_SRC = '^ {0,3}((?:-[ \\t]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)';
const HR_RE = rx(HR_SRC, '');
const FENCES_PAT = ' {0,3}(?:`{3,}|~{3,})';
const BLOCKQUOTE_PAT = ' {0,3}>';
const HEADING_PAT = ' {0,3}#{1,6}(?:\\s|$)';
const HR_PAT = ' {0,3}(?:(?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)';
const HTML_LINE_PAT = ' {0,3}<[^\\n>]+>\\n';
const TABLE_LINE_PAT = ' {0,3}\\|?(?:[:\\- ]*\\|)+[\\:\\- ]*\\n';

// Paragraph base: first line plus continuation lines that do not start a
// block construct and are not blank.
const PARA_BASE = '^([^\\n]+(?:\\n(?!hr|heading|lheading|blockquote|fences|list|html|table|[ \\t]+\\n)[^\\n]+)*)';
const HTML_INLINE_PAT = ' {0,3}(?:</?(?:tag)(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)';

const TABLE_SRC = compose(
  '^ *([^\\n ].*)\\n {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)(?:\\n((?:(?! *\\n|hr|heading|blockquote|code|fences|list|html).*(?:\\n|$))*)\\n*|$)',
  [
    ['hr', HR_RE],
    ['heading', HEADING_PAT],
    ['blockquote', BLOCKQUOTE_PAT],
    ['code', '(?: {4}| {0,3}\\t)[^\\n]'],
    ['fences', ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)'],
    ['list', ' {0,3}(?:[*+-]|1[.)])[ \\t]'],
    ['html', HTML_INLINE_PAT],
    [/tag/g, BLOCK_TAGS],
  ],
);

// Setext heading base.
const SETEXT_BASE = '^(?!bull|blockCode|fences|blockquote|heading|html|table)((?:.|\\n(?!\\s*?\\n|bull|fences|blockquote|heading|hr|html|table))+?)\\n {0,3}(=+|-+)[ \\t]*(?:\\n+|$)';
const LHEADING_SRC = compose(SETEXT_BASE, [
  [/bull/g, BULLET],
  [/blockCode/g, '(?: {4}| {0,3}\\t)'],
  [/fences/g, FENCES_PAT],
  [/blockquote/g, BLOCKQUOTE_PAT],
  [/heading/g, HEADING_PAT],
  [/hr/g, HR_PAT],
  [/html/g, HTML_LINE_PAT],
  [/table/g, TABLE_LINE_PAT],
]);

function paragraphSrc(listPat, withTable) {
  const reps = [
    ['hr', HR_RE],
    ['heading', HEADING_PAT],
    ['|lheading', ''],
    ['blockquote', BLOCKQUOTE_PAT],
    ['fences', ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)'],
    ['list', listPat],
    ['html', HTML_INLINE_PAT],
    [/tag/g, BLOCK_TAGS],
  ];
  if (withTable) reps.splice(3, 0, ['table', rx(TABLE_SRC, '')]);
  else reps.splice(3, 0, ['|table', '']);
  return compose(PARA_BASE, reps);
}

// The paragraph form used inside blockquotes (no table stop, any bullet).
const PARA_IN_QUOTE_SRC = paragraphSrc(' {0,3}(?:[*+-]|\\d{1,9}[.)])(?:[ \\t]|\\n|$)', false);
// The paragraph form used at top level (table stop, "1." bullets only).
const PARA_TOP_SRC = paragraphSrc(' {0,3}(?:[*+-]|1[.)])[ \\t]+[^ \\t\\n]', true);

// Label inside [..] for links and reference definitions.
const LABEL_RE = rx('(?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\\\n]|\\n(?![ \\t]*\\n))+', '');
const BRACKETED = '\\[(?:\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]';
// The longer label form used when scanning for reference links.
const LT_SRC = compose(
  '(?:[^\\[\\]\\\\`]*(?:\\[(?:brackets|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\]))){0,999}?[^\\[\\]\\\\`]*?',
  [['brackets', BRACKETED]],
);
const LINK_LABEL_SRC = compose(
  '(?:\\[(?:brackets|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\])|[^\\[\\]\\\\`])*?',
  [['brackets', BRACKETED]],
);
const REF_LABEL_SRC = '(?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\]){1,999}';

// Block-level patterns (sticky: they always match at the current index).
const reSpace = rx('(?:[ \\t]*(?:\\n|$))+', 'y');
const reCode = rx('((?: {4}| {0,3}\\t)[^\\n]+(?:\\n(?:[ \\t]*(?:\\n|$))*)?)+', 'y');
const reFences = rx(' {0,3}(`{3,}(?=[^`\\n]*(?:\\n|$))|~{3,})([^\\n]*)(?:\\n|$)(?:|([\\s\\S]*?)(?:\\n|$))(?: {0,3}(?:(?=`)\\1`*|(?=~)\\1~*) *(?=\\n|$)|$)', 'y');
const reHeading = rx(' {0,3}(#{1,6})(?=\\s|$)(.*)(?:\\n+|$)', 'y');
const reHr = rx(HR_SRC.slice(1), 'y');
const reList = rx('(' + BULLET + ')([ \\t][^\\n]*?)?(?:\\n|$)', 'y');
const reText = rx('[^\\n]+', 'y');
const reHtmlBlock = rx(compose(
  ' {0,3}(?:<(script|pre|style|textarea)[\\s>][\\s\\S]*?(?:</\\1>[^\\n]*\\n*|$)|comment[^\\n]*(\\n+|$)|<\\?[\\s\\S]*?(?:\\?>[^\\n]*\\n*|$)|<![A-Z][\\s\\S]*?(?:>[^\\n]*\\n*|$)|<!\\[CDATA\\[[\\s\\S]*?(?:\\]\\]>[^\\n]*\\n*|$)|</?(tag)(?:[ \\t]+|\\n|/?>)[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?:attribute)*? */?>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)|</[a-z][a-z0-9-]*\\s*>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$))',
  [
    ['comment', rx('<!--(?:-?>|[\\s\\S]*?-->)', '')],
    ['tag', BLOCK_TAGS],
    ['attribute', rx(' +[a-zA-Z:_][\\w.:-]*(?: *= *"[^"\\n]*"| *= *\'[^\'\\n]*\'| *= *[^\\s"\'=<>`]+)?', '')],
  ],
), 'iy');
const reDef = rx(compose(
  ' {0,3}\\[(label)\\]: *(?:\\n[ \\t]*)?([^<\\s][^\\s]*|<.*?>)(?:(?: +(?:\\n[ \\t]*)?| *\\n[ \\t]*)(title))? *(?:\\n+|$)',
  [
    ['label', LABEL_RE],
    ['title', rx('(?:"(?:\\\\[\\s\\S]|[^"\\\\])*"|\'(?:\\\\[\\s\\S]|[^\'\\\\\\n]|\\n(?!\\n))*\'|\\((?:\\\\[\\s\\S]|[^()\\\\])*\\))', '')],
  ],
), 'y');
const reTable = rx(TABLE_SRC.slice(1), 'y');
const reLheading = rx(LHEADING_SRC.slice(1), 'y');
const reParagraphTop = rx(PARA_TOP_SRC.slice(1), 'y');
const reParagraphQuote = rx(PARA_IN_QUOTE_SRC.slice(1), 'y');
const reBlockquote = rx(compose(
  '(?: {0,3}> ?(?:(?![ \\t]*(?:\\n|$))(paragraph)|[^\\n]*)(?:\\n|$))+',
  [['paragraph', rx(PARA_IN_QUOTE_SRC, '')]],
), 'y');

// Block patterns used with .test on a single line (no sticky needed).
const reBlockquoteStart = /^ {0,3}>/;
const reBlankLine = /^[ \t]*$/;
const reDoubleBlank = /\n[ \t]*\n[ \t]*$/;
const reAnyLine = /\n.*\n/;
const reNonSpace = /[^ ]/;
const reLeadingSpaceTab = /^[ \t]+/;
const reTabGlobal = /\t/g;
const reCodeRemoveIndent = /^(?: {0,3}\t| {1,4})/gm;
const reIndentCodeComp = /^(\s+)(?:```)/;
const reBeginningSpace = /^\s+/;
const reEndingHash = /#$/;
const reEndingSpaceTab = /[ \t]$/;
const reStartAngle = /^</;
const reEndAngle = />$/;
const reHrefBrackets = /^<(.*)>$/;
const reTableDelim = /[:|]/;
const reTableAlignChars = /^\||\| *$/g;
const reTableRowBlank = /\n[ \t]*$/;
const reAlignRight = /^ *-+: *$/;
const reAlignCenter = /^ *:-+: *$/;
const reAlignLeft = /^ *:-+ *$/;
const reListIsTask = /^\[[ xX]\][ \t]+\S/;
const reListReplaceTask = /^\[[ xX]\][ \t]+/;
const reListTaskCheckbox = /\[[ xX]\]/;
const reListNesting = /^ {1,4}(?=( {4})*[^ ])/g;
const reSetextLine = /^ {0,3}(?:=+|-+) *$/;
// Cheap pre-test for a setext underline somewhere ahead: the scan stops at
// the first blank line or underline-like line, whichever comes first. The
// full lheading pattern needs `\n {0,3}(=+|-+)[ \t]*(?:\n+|$)` before any
// blank line, so a miss (or a blank line first) proves it cannot match.
const reSetextOrBlank = /\n[ \t]*\n|\n {0,3}[=-]+[ \t]*(?:\n|$)/g;
const reBlockquoteMarkerWs = /^( {0,3}>)([ \t]+)/gm;
const reBlockquoteSetext = /\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g;
const reBlockquoteSetext2 = /^ {0,3}>[ \t]?/gm;
const reNotSpaceStart = /^\S*/;
const reEndingNewline = /\n$/;
const reSpaceLine = /^ +$/gm;
const reMultipleSpace = /\s+/g;

// Per-indent block-start patterns inside list items (cached by indent).
// The indent is clamped to 0..3 (the parameter is really n-1, capped).
const indentCache = new Map();
function indentRes(n) {
  const cn = Math.max(0, Math.min(3, n - 1));
  let c = indentCache.get(cn);
  if (!c) {
    c = {
      nextBullet: rx(`^ {0,${cn}}(?:[*+-]|\\d{1,9}[.)])((?:[ \\t][^\\n]*)?(?:\\n|$))`, ''),
      hr: rx(`^ {0,${cn}}((?:-[ \\t]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)`, ''),
      fences: rx(`^ {0,${cn}}(?:\`\`\`|~~~)`, ''),
      heading: rx(`^ {0,${cn}}#{1,6}(?:\\s|$)`, ''),
      html: rx(`^ {0,${cn}}(?:</?(?:${BLOCK_TAGS})(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`, 'i'),
      blockquote: rx(`^ {0,${cn}}>`, ''),
    };
    indentCache.set(cn, c);
  }
  return c;
}
function listItemRe(bulletPat) {
  return rx(`( {0,3}${bulletPat})((?:[\\t ][^\\n]*)?(?:\\n|$))`, 'y');
}

// ------------------------------------------------------- inline patterns

const ANY_PUNCT = '[\\p{P}\\p{S}]';
const reAnyPunct = rx('\\\\(' + ANY_PUNCT + ')', 'gu');
const reEscape = rx('\\\\([!"#$%&\'()*+,\\-./:;<=>?@\\[\\]\\\\^_`{|}~])', 'y');
const reCodeSpan = rx('(`+)([^`]|[^`][\\s\\S]*?[^`])\\1(?!`)', 'y');
const reBr = rx('( {2,}|\\\\)\\n(?!\\s*$)[ \\t]*', 'y');
const reTag = rx(stripCaret(compose(
  'comment|^</[a-zA-Z][a-zA-Z0-9-]*\\s*>|^<[a-zA-Z][a-zA-Z0-9-]*(?:attribute)*?\\s*/?>|^<\\?[\\s\\S]*?\\?>|^<![a-zA-Z]+\\s[\\s\\S]*?>|^<!\\[CDATA\\[[\\s\\S]*?\\]\\]>',
  [
    ['comment', rx('<!--(?:-?>|[\\s\\S]*?-->)', '')],
    ['attribute', rx('\\s+[a-zA-Z:_][\\w.:-]*(?:\\s*=\\s*"[^"]*"|\\s*=\\s*\'[^\']*\'|\\s*=\\s*[^\\s"\'=<>`]+)?', '')],
  ],
)), 'y');
const reAutolink = rx(stripCaret(
  '^<([a-zA-Z][a-zA-Z0-9+.-]{1,31}:[^\\s\\x00-\\x1f<>]*|[a-zA-Z0-9.!#$%&\'*+\\/=?^_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_]))>',
), 'y');
const EMAIL_IT = '[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])';
const EMAIL_PROTO = '(?:mailto:' + EMAIL_IT + '|xmpp:' + EMAIL_IT + '(?:\\/[A-Za-z0-9@.]+)?)';
const reUrl = rx(compose(
  '(?:mailto:email|xmpp:email(?:\\/[A-Za-z0-9@.]+)?)|((?:protocol):\\/\\/|www\\.)(?:[a-zA-Z0-9\\-]+\\.?)+[^\\s<]*|[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])',
  [
    ['protocol', rx('[hH][tT][tT][pP][sS]?|[fF][tT][pP]', '')],
    [/email/g, EMAIL_IT],
  ],
), 'y');
const reBackpedal = /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+/;
const reLink = rx(compose(
  '!?\\[(label)\\]\\([ \\t\\n]*(href)(?:(?:[ \\t]+(?:\\n[ \\t]*)?|\\n[ \\t]*)(title))?[ \\t\\n]*\\)',
  [
    ['label', rx(LINK_LABEL_SRC, '')],
    ['href', rx('<(?:\\\\.|[^\\n<>\\\\])+>|[^ \\t\\n\\x00-\\x1f]+|(?=\\))', '')],
    ['title', rx('"(?:\\\\[\\s\\S]|[^"\\\\])*"|\'(?:\\\\[\\s\\S]|[^\'\\\\])*\'|\\((?:\\\\[\\s\\S]|[^)\\\\])*\\)', '')],
  ],
), 'y');
const reReflink = rx(compose('!?\\[(label)\\]\\[(ref)\\]', [
  ['label', rx(LINK_LABEL_SRC, '')],
  ['ref', rx(REF_LABEL_SRC, '')],
]), 'y');
const reNolink = rx(compose('!?\\[(ref)\\](?:\\[\\])?', [
  ['ref', rx(REF_LABEL_SRC, '')],
]), 'y');

// Emphasis delimiters (GFM flavour).
const reEmLDelim = rx(stripCaret(compose(
  '^(?:\\*+(?:((?!\\*)punct)|([^\\s*]))?)|^_+(?:((?!_)punct)|([^\\s_]))?',
  [[/punct/g, '(?!~)' + ANY_PUNCT]],
)), 'yu');
const reEmRDelimAst = rx(compose(
  '^[^_*]*?__[^_*]*?\\*[^_*]*?(?=__)|[^*]+(?=[^*])|(?!\\*)punct(\\*+)(?=[\\s]|$)|notPunctSpace(\\*+)(?!\\*)(?=punctSpace|$)|(?!\\*)punctSpace(\\*+)(?=notPunctSpace)|[\\s](\\*+)(?!\\*)(?=punct)|(?!\\*)punct(\\*+)(?!\\*)(?=punct)|notPunctSpace(\\*+)(?=notPunctSpace)',
  [
    [/notPunctSpace/g, '(?:[^\\s\\p{P}\\p{S}]|~)'],
    [/punctSpace/g, '(?!~)[\\s\\p{P}\\p{S}]'],
    [/punct/g, '(?!~)' + ANY_PUNCT],
  ],
), 'gu');
const reEmRDelimUnd = rx(compose(
  '^[^_*]*?\\*\\*[^_*]*?_[^_*]*?(?=\\*\\*)|[^_]+(?=[^_])|(?!_)punct(_+)(?=[\\s]|$)|notPunctSpace(_+)(?!_)(?=punctSpace|$)|(?!_)punctSpace(_+)(?=notPunctSpace)|[\\s](_+)(?!_)(?=punct)|(?!_)punct(_+)(?!_)(?=punct)',
  [
    [/notPunctSpace/g, '[^\\s\\p{P}\\p{S}]'],
    [/punctSpace/g, '[\\s\\p{P}\\p{S}]'],
    [/punct/g, ANY_PUNCT],
  ],
), 'gu');
const reDelLDelim = rx(stripCaret('^~~?(?:((?!~)' + ANY_PUNCT + ')|[^\\s~])'), 'yu');
const reDelRDelim = rx(compose(
  '^[^~]+(?=[^~])|(?!~)punct(~~?)(?=[\\s]|$)|notPunctSpace(~~?)(?!~)(?=punctSpace|$)|(?!~)punctSpace(~~?)(?=notPunctSpace)|[\\s](~~?)(?!~)(?=punct)|(?!~)punct(~~?)(?!~)(?=punct)|notPunctSpace(~~?)(?=notPunctSpace)',
  [
    [/notPunctSpace/g, '[^\\s\\p{P}\\p{S}]'],
    [/punctSpace/g, '[\\s\\p{P}\\p{S}]'],
    [/punct/g, ANY_PUNCT],
  ],
), 'gu');

// Masking patterns for the emphasis scan (they hide links, code spans and
// tags so a delimiter inside one cannot close an emphasis run).
const reReflinkSearch = rx(compose(
  '!?\\[(label)\\]\\[(ref)\\]|!?\\[(ref)\\](?:\\[\\])?(?!\\()',
  [
    ['label', rx(LT_SRC, '')],
    [/ref/g, rx(REF_LABEL_SRC, '')],
  ],
), 'g');
const reAnyPunctOutsideCode = rx('(`+)(?:[^`]|[^`][\\s\\S]*?[^`])\\1(?!`)|`+|\\\\(' + ANY_PUNCT + ')', 'gu');
const reBlockSkip = rx(
  '\\[(?:[^\\[\\]`]|(?<a>`+)[^`]+\\k<a>(?!`))*?\\]\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)]|\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)])*\\))*\\)|(?<!`)()(?<b>`+)[^`]+\\k<b>(?!`)|<(?! )[^<>]*?>',
  'g',
);
const reLinkTest = rx(compose(
  '!?\\[(label)\\]\\([ \\t\\n]*(href)(?:(?:[ \\t]+(?:\\n[ \\t]*)?|\\n[ \\t]*)(title))?[ \\t\\n]*\\)',
  [
    ['label', rx(LINK_LABEL_SRC, '')],
    ['href', rx('<(?:\\\\.|[^\\n<>\\\\])+>|[^ \\t\\n\\x00-\\x1f]+|(?=\\))', '')],
    ['title', rx('"(?:\\\\[\\s\\S]|[^"\\\\])*"|\'(?:\\\\[\\s\\S]|[^\'\\\\])*\'|\\((?:\\\\[\\s\\S]|[^)\\\\])*\\)', '')],
  ],
), '');
const reStartATag = /^<a /i;
const reEndATag = /^<\/a>/i;
const reStartPreTag = /^<(pre|code|kbd|script)(\s|>)/i;
const reEndPreTag = /^<\/(pre|code|kbd|script)(\s|>)/i;
const reOutputLink = /\\([\[\]])/g;
const EMAIL_CHARS = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789.!#$%&'*+/=?_`{|}~-";

// ------------------------------------------------------------ inline engine
// mode 0 renders HTML, mode 1 renders plain text (for image alt text).

function linkInText(src, links) {
  if (!src.includes('[')) return false;
  for (const m of src.matchAll(reBlockSkip)) {
    if (reLinkTest.test(m[0]) && src.charAt(m.index - 1) !== '!') return true;
  }
  for (const m of src.matchAll(reReflinkSearch)) {
    const s = m[0];
    const r = s.lastIndexOf('[');
    if (
      !(s.charAt(0) === '!' || !Object.hasOwn(links, normLabel(s.slice(r + 1, -1)))) &&
      !(r > 1 && linkInText(s.slice(1, r - 1), links))
    ) return true;
  }
  return false;
}

// Hide links, code spans and tags from the emphasis scan by replacing
// their insides with filler, keeping every position aligned.
function maskEm(src, links, hasLinks) {
  let t = src;
  if (hasLinks && src.includes('[')) {
    const hide = (m) => {
      const o = m.lastIndexOf('[');
      if (!Object.hasOwn(links, normLabel(m.slice(o + 1, -1)))) return m;
      if (o > 1 && m.charAt(0) !== '!') {
        const inner = m.slice(1, o - 1);
        if (linkInText(inner, links)) {
          return '[' + inner.replace(reReflinkSearch, hide) + '][' + 'a'.repeat(m.length - o - 2) + ']';
        }
      }
      return '[' + 'a'.repeat(m.length - 2) + ']';
    };
    t = t.replace(reReflinkSearch, hide);
  }
  // Code spans and escapes can only match where a backtick or backslash
  // occurs; inline links/tags only where [ or < occurs. Skipping the
  // whole-string replaces when those characters are absent is exact.
  // This replace only changes the string in two cases: an escape (needs a
  // backslash) or a backtick inside a code span's content (needs a `` opener,
  // since a single-backtick span always closes at the first interior
  // backtick). Otherwise it returns every match unchanged.
  if (t.includes('\\') || t.includes('``')) {
    t = t.replace(reAnyPunctOutsideCode, (m, g1, g2) => {
      if (g2) return '+'.repeat(m.length);
      if (g1) return g1 + m.slice(g1.length, -g1.length).replace(/`/g, '+') + g1;
      return m;
    });
  }
  if (t.includes('[') || t.includes('`') || t.includes('<')) {
    t = t.replace(reBlockSkip, (m, g1, g2) => {
      const o = g2 ? g2.length : 0;
      return m.slice(0, o) + '[' + 'a'.repeat(m.length - o - 2) + ']';
    });
  }
  return t;
}

// Last index where an emphasis / strikethrough run could close: the first
// character of a run, provided the character before the run is not a space.
function lastClosers(masked) {
  const em = { '*': -1, '_': -1 };
  let del = -1;
  const n = masked.length;
  for (let s = 0; s < n; s++) {
    const r = masked[s];
    if (r !== '*' && r !== '_' && r !== '~') continue;
    const o = s === 0 ? '\n' : masked[s - 1];
    let i = s + 1;
    while (i < n && masked[i] === r) i++;
    if (o !== ' ' && o !== '\t' && o !== '\n' && o !== '\r' && o !== '\f') {
      if (r === '~') del = s;
      else em[r] = s;
    }
    s = i - 1;
  }
  return { em, del };
}

function tryEmStrong(src, masked, closers, pos, prevChar, st, links, mode) {
  const r = src[pos];
  const code = src.charCodeAt(pos);
  // No closer can exist at or after this position.
  if (closers.em[r] < pos) return null;
  // The delimiter run and the character after it.
  let q = pos + 1;
  while (src.charCodeAt(q) === code) q++;
  // A run at the very end cannot open: the left-delimiter pattern would
  // match with every group empty.
  if (q >= src.length) return null;
  // Intraword _: an alphanumeric character on both sides of the run cannot
  // open (the left-delimiter pattern's fourth group plus the alphanumeric
  // previous character).
  if (r === '_' && prevChar !== '' && alphaNumRe.test(prevChar) && alphaNumRe.test(src[q])) return null;
  reEmLDelim.lastIndex = pos;
  const s = reEmLDelim.exec(src);
  if (!s || (!s[1] && !s[2] && !s[3] && !s[4])) return null;
  const o = prevChar === r;
  const i = pos;
  let l = i;
  while (l > 0 && masked[l - 1] === r) l--;
  const p = l === 0 ? '' : masked[l - 1];
  const h = p === '*' || p === '_' || isPunctChar(p);
  let n = prevChar;
  if (l < i) n = p;
  const u = l < i ? h : isPunctChar(n);
  if (s[4] && n !== '' && alphaNumRe.test(n)) return null;
  const d = s[1] || s[3] || '';
  if (!d || !n || u) {
    const k = s[0].length - 1 - (s[0].charCodeAt(s[0].length - 1) >= 0xDC00 && s[0].charCodeAt(s[0].length - 1) <= 0xDFFF ? 1 : 0);
    let m = k;
    let f = 0;
    const y = i - l + k;
    const R = p.trim() !== '' && (!!d || (r === '*' && !h));
    if (r !== '*' && r !== '_') return null;
    const A = r === '*' ? reEmRDelimAst : reEmRDelimUnd;
    const v = closers.em[r];
    const Q = pos + k;
    if (v < Q) return null;
    const t2 = masked.slice(pos + k);
    const ee = v - Q;
    A.lastIndex = 0;
    let ms;
    while ((ms = A.exec(t2)) !== null && !(ms.index > ee)) {
      const g = ms[1] || ms[2] || ms[3] || ms[4] || ms[5] || ms[6];
      if (!g) continue;
      let b = g.length;
      if (ms[3] || ms[4]) { m += b; continue; }
      if (ms[5] || ms[6] || R) {
        if (o && (ms[5] || ms[6])) break;
        if (y % 3 && !((y + b) % 3)) { f += b; continue; }
      }
      m -= b;
      if (m > 0) continue;
      b = Math.min(b, b + m + f);
      const te = ms[0].codePointAt(0) > 0xFFFF ? 2 : 1;
      const M = src.slice(pos, pos + k + ms.index + te + b);
      if (Math.min(k, b) % 2) {
        const U = M.slice(1, -1);
        const inner = inlineHTML(U, links, st, mode);
        return { len: M.length, html: mode === 1 ? inner : '<em>' + inner + '</em>' };
      }
      const ne = M.slice(2, -2);
      const inner = inlineHTML(ne, links, st, mode);
      return { len: M.length, html: mode === 1 ? inner : '<strong>' + inner + '</strong>' };
    }
  }
  return null;
}

function tryDel(src, masked, closers, pos, prevChar, st, links, mode) {
  // No closer can exist at or after this position.
  if (closers.del < pos) return null;
  reDelLDelim.lastIndex = pos;
  const s = reDelLDelim.exec(src);
  if (!s) return null;
  if (!(s[1] || '') || !prevChar || isPunctChar(prevChar)) {
    const o = s[0].length - 1 - (s[0].charCodeAt(s[0].length - 1) >= 0xDC00 && s[0].charCodeAt(s[0].length - 1) <= 0xDFFF ? 1 : 0);
    let p = o;
    const u = closers.del;
    const d = pos + o;
    if (u < d) return null;
    const t2 = masked.slice(pos + o);
    const k = u - d;
    reDelRDelim.lastIndex = 0;
    let ms;
    while ((ms = reDelRDelim.exec(t2)) !== null && !(ms.index > k)) {
      const g = ms[1] || ms[2] || ms[3] || ms[4] || ms[5] || ms[6];
      if (!g) continue;
      let l = g.length;
      if (l !== o) continue;
      if (ms[3] || ms[4]) { p += l; continue; }
      p -= l;
      if (p > 0) continue;
      l = Math.min(l, l + p);
      const gg = ms[0].codePointAt(0) > 0xFFFF ? 2 : 1;
      const b = src.slice(pos, pos + o + ms.index + gg + l);
      const m = b.slice(o, -o);
      const inner = inlineHTML(m, links, st, mode);
      return { len: b.length, html: mode === 1 ? inner : '<del>' + inner + '</del>' };
    }
  }
  return null;
}

function tryEscape(src, pos, mode) {
  reEscape.lastIndex = pos;
  const m = reEscape.exec(src);
  if (!m) return null;
  const ch = m[1];
  return { len: m[0].length, html: mode === 1 ? ch : esc(ch) };
}

function tryCodeSpan(src, pos, mode) {
  reCodeSpan.lastIndex = pos;
  const m = reCodeSpan.exec(src);
  if (!m) return null;
  let text = m[2].replace(/\n/g, ' ');
  if (/[^ ]/.test(text) && text.charAt(0) === ' ' && text.charAt(text.length - 1) === ' ') {
    text = text.substring(1, text.length - 1);
  }
  return { len: m[0].length, html: mode === 1 ? text : '<code>' + esc(text, true) + '</code>' };
}

function tryBr(src, pos, mode) {
  reBr.lastIndex = pos;
  const m = reBr.exec(src);
  if (!m) return null;
  return { len: m[0].length, html: mode === 1 ? '' : '<br>' };
}

function tryTag(src, pos, st) {
  reTag.lastIndex = pos;
  const m = reTag.exec(src);
  if (!m) return null;
  const raw = m[0];
  if (!st.inLink && reStartATag.test(raw)) st.inLink = true;
  else if (st.inLink && reEndATag.test(raw)) st.inLink = false;
  if (!st.inRawBlock && reStartPreTag.test(raw)) st.inRawBlock = true;
  else if (st.inRawBlock && reEndPreTag.test(raw)) st.inRawBlock = false;
  return { len: raw.length, html: raw };
}

function tryAutolink(src, pos, mode) {
  reAutolink.lastIndex = pos;
  const m = reAutolink.exec(src);
  if (!m) return null;
  const text = m[1];
  const href = m[2] === '@' ? 'mailto:' + text : text;
  if (mode === 1) return { len: m[0].length, html: text };
  const clean = cleanUrl(href);
  if (clean === null) return { len: m[0].length, html: esc(text, true) };
  return { len: m[0].length, html: '<a href="' + esc(clean, true) + '">' + esc(text, true) + '</a>' };
}

function tryUrl(src, pos, mode) {
  reUrl.lastIndex = pos;
  const m = reUrl.exec(src);
  if (!m) return null;
  let raw;
  let text;
  let href;
  if (m[2] === '@') {
    raw = m[0];
    text = m[0];
    href = 'mailto:' + m[0];
  } else {
    raw = m[0];
    let r;
    do {
      r = raw;
      const b = reBackpedal.exec(raw);
      raw = b ? b[0] : '';
    } while (r !== raw);
    text = raw;
    href = m[1] === 'www.' ? 'http://' + raw : raw;
  }
  if (mode === 1) return { len: raw.length, html: text };
  const clean = cleanUrl(href);
  if (clean === null) return { len: raw.length, html: esc(text, true) };
  return { len: raw.length, html: '<a href="' + esc(clean, true) + '">' + esc(text, true) + '</a>' };
}

// Does a "<" inside a link label start a tag/autolink that runs past the
// end of the label? Then the "[" is not a link at all.
function linkHasTag(src, pos, label, skip) {
  if (!label.includes('<')) return false;
  for (let s = 0; s < label.length; s++) {
    if (label[s] === '\\') { s++; continue; }
    if (label[s] === '`') {
      reCodeSpan.lastIndex = 0;
      const m = reCodeSpan.exec(label.slice(s));
      if (m) { s += m[0].length - 1; continue; }
    }
    if (label[s] !== '<') continue;
    const at = pos + skip + s;
    reTag.lastIndex = at;
    const o = reTag.exec(src);
    if (o) {
      if (o[0].length > label.length - s) return true;
      s += o[0].length - 1;
      continue;
    }
    reAutolink.lastIndex = at;
    const a = reAutolink.exec(src);
    if (a) {
      if (a[0].length > label.length - s) return true;
      s += a[0].length - 1;
    }
  }
  return false;
}

// Shared link/image construction: parse the label text inline, refuse a
// link whose label already holds a link, and render the anchor or image.
function buildLink(isImage, href, title, labelText, len, st, links, mode) {
  const savedInLink = st.inLink;
  const savedEmitted = st.linkEmitted;
  const savedRaw = st.inRawBlock;
  st.inLink = true;
  st.linkEmitted = false;
  const inner = inlineHTML(labelText, links, st, isImage ? 1 : mode);
  const k = st.linkEmitted;
  st.linkEmitted = savedEmitted;
  st.inLink = savedInLink;
  if (!isImage) {
    if (k) {
      st.inRawBlock = savedRaw;
      return null;
    }
    st.linkEmitted = true;
  }
  if (mode === 1) return { len, html: inner };
  if (isImage) {
    const clean = cleanUrl(href);
    if (clean === null) return { len, html: esc(inner) };
    let out = '<img src="' + esc(clean) + '" alt="' + esc(inner) + '"';
    if (title) out += ' title="' + esc(title) + '"';
    return { len, html: out + '>' };
  }
  const clean = cleanUrl(href);
  if (clean === null) return { len, html: inner };
  let out = '<a href="' + esc(clean) + '"';
  if (title) out += ' title="' + esc(title) + '"';
  return { len, html: out + '>' + inner + '</a>' };
}

function tryInlineLink(src, pos, st, links, mode) {
  if (st.parenPossible === false) return null;
  reLink.lastIndex = pos;
  const m = reLink.exec(src);
  if (!m) return null;
  const isImage = m[0].charAt(0) === '!';
  const skip = isImage ? 2 : 1;
  if (linkHasTag(src, pos, m[1], skip)) return null;
  let raw = m[0];
  let hrefPart = m[2];
  let titlePart = m[3];
  const s = hrefPart.trim();
  if (reStartAngle.test(s)) {
    if (!reEndAngle.test(s)) return null;
    const l = rtrimCh(s.slice(0, -1), 92);
    if ((s.length - l.length) % 2 === 0) return null;
  } else {
    const close = findClose(hrefPart, '()');
    if (close === -2) return null;
    if (close > -1) {
      const h = (isImage ? 5 : 4) + m[1].length + close;
      hrefPart = hrefPart.substring(0, close);
      raw = raw.substring(0, h).trim();
      titlePart = '';
    }
  }
  const r = rtrimCh(raw.slice(0, -1), 92);
  if ((raw.length - r.length) % 2 === 0) return null;
  let href = hrefPart;
  let title = titlePart ? titlePart.slice(1, -1) : '';
  href = href.trim();
  if (reStartAngle.test(href)) href = href.slice(1, -1);
  href = href ? href.replace(reAnyPunct, '$1') : '';
  title = title ? title.replace(reAnyPunct, '$1') : '';
  const labelText = m[1].replace(reOutputLink, '$1');
  return buildLink(isImage, href, title, labelText, raw.length, st, links, mode);
}

function tryRefLink(src, pos, st, links, mode) {
  reReflink.lastIndex = pos;
  let m = reReflink.exec(src);
  let isImage = false;
  if (m) {
    isImage = m[0].charAt(0) === '!';
  } else {
    reNolink.lastIndex = pos;
    m = reNolink.exec(src);
    if (!m) return null;
    isImage = m[0].charAt(0) === '!';
  }
  const skip = isImage ? 2 : 1;
  if (linkHasTag(src, pos, m[1], skip)) return null;
  const ref = normLabel(m[2] || m[1]);
  const def = links[ref];
  if (!def) {
    const ch = src[pos];
    return { len: 1, html: mode === 1 ? ch : esc(ch) };
  }
  const labelText = m[1].replace(reOutputLink, '$1');
  return buildLink(isImage, def.href, def.title, labelText, m[0].length, st, links, mode);
}

function isEmailCharCode(c) {
  return (
    (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122) ||
    c === 46 || c === 95 || c === 43 || c === 45 || c === 33 || c === 35 ||
    c === 36 || c === 37 || c === 38 || c === 39 || c === 42 || c === 47 ||
    c === 61 || c === 63 || c === 96 || c === 123 || c === 124 || c === 125 || c === 126
  );
}

// Could an extended autolink (www., http://, mailto:, email) start here?
function isUrlStart(src, pos, ch) {
  if (ch === 104 || ch === 72) {
    // http:// or https:// (else fall through: the word may be an email)
    const a = src.charCodeAt(pos + 1);
    const b = src.charCodeAt(pos + 2);
    const c = src.charCodeAt(pos + 3);
    if ((a === 116 || a === 84) && (b === 116 || b === 84) && (c === 112 || c === 80)) {
      const d = src.charCodeAt(pos + 4);
      if (d === 58) return true;
      if ((d === 115 || d === 83) && src.charCodeAt(pos + 5) === 58) return true;
    }
  }
  if (ch === 102 || ch === 70) {
    // ftp:// (else fall through: the word may be an email)
    if (
      (src.charCodeAt(pos + 1) === 116 || src.charCodeAt(pos + 1) === 84) &&
      (src.charCodeAt(pos + 2) === 112 || src.charCodeAt(pos + 2) === 80) &&
      src.charCodeAt(pos + 3) === 58
    ) return true;
  }
  if (ch === 119 || ch === 87) {
    // www. (only after start, space, *, _, ~ or () — else fall through)
    if (src.charCodeAt(pos + 1) === 119 && src.charCodeAt(pos + 2) === 119 && src.charCodeAt(pos + 3) === 46) {
      if (pos === 0) return true;
      const p = src.charCodeAt(pos - 1);
      if (p === 32 || p === 9 || p === 10 || p === 42 || p === 95 || p === 126 || p === 40) return true;
    }
  }
  if (ch === 109 || ch === 77) {
    // mailto: (checked by char code, no allocation)
    if (
      (src.charCodeAt(pos + 1) === 97 || src.charCodeAt(pos + 1) === 65) &&
      (src.charCodeAt(pos + 2) === 105 || src.charCodeAt(pos + 2) === 73) &&
      (src.charCodeAt(pos + 3) === 108 || src.charCodeAt(pos + 3) === 76) &&
      (src.charCodeAt(pos + 4) === 116 || src.charCodeAt(pos + 4) === 84) &&
      (src.charCodeAt(pos + 5) === 111 || src.charCodeAt(pos + 5) === 79) &&
      src.charCodeAt(pos + 6) === 58
    ) return true;
  }
  if (ch === 120 || ch === 88) {
    // xmpp: (checked by char code, no allocation)
    if (
      (src.charCodeAt(pos + 1) === 109 || src.charCodeAt(pos + 1) === 77) &&
      (src.charCodeAt(pos + 2) === 112 || src.charCodeAt(pos + 2) === 80) &&
      (src.charCodeAt(pos + 3) === 112 || src.charCodeAt(pos + 3) === 80) &&
      src.charCodeAt(pos + 4) === 58
    ) return true;
  }
  // Email address: at a word start, with an @ ahead in the word.
  if (!isEmailCharCode(ch)) return false;
  if (pos > 0 && isEmailCharCode(src.charCodeAt(pos - 1))) return false;
  let q = pos;
  while (q < src.length) {
    const c = src.charCodeAt(q);
    if (c === 64) return true;
    if (!isEmailCharCode(c)) return false;
    q++;
  }
  return false;
}

function inlineHTML(src, links, st, mode) {
  const savedParen = st.parenPossible;
  st.parenPossible = savedParen && src.includes(')');
  try {
    return inlineScan(src, links, st, mode);
  } finally {
    st.parenPossible = savedParen;
  }
}

// Finds the next position where an inline construct could start: a delimiter
// or tag character, a hard break, a protocol, or an email word at a word
// start (the lookbehind keeps the email scan linear: without it the greedy
// run backtracks once per character of every long word).
const reNextSpecial = /[\\<\[!*_`~]| {2,}\n|[hH][tT][tT][pP][sS]?:\/\/|[fF][tT][pP]:\/\/|www\.|mailto:|xmpp:|(?<![A-Za-z0-9.!#$%&'*+\/=?_`{|}~-])[A-Za-z0-9.!#$%&'*+\/=?_`{|}~-]+@/g;

function inlineScan(src, links, st, mode) {
  const n = src.length;
  let masked = null;
  let closers = null;
  const needMask = () => {
    if (masked === null) {
      // needMask is only called from an emphasis / strikethrough attempt,
      // so the string always contains one of *, _, ~ here.
      masked = maskEm(src, links, st.hasLinks);
      closers = lastClosers(masked);
    }
    return masked;
  };
  const out = [];
  let textStart = 0;
  let tokStart = 0;
  let prevChar = '';
  const flushText = (end, raw) => {
    if (end > textStart) {
      let run = src.slice(textStart, end);
      if (!raw) run = unescNumeric(run);
      out.push(mode === 1 ? run : esc(run));
    }
  };
  // The previous character of the text token ending at a construct attempt
  // (marked leaves it unchanged when the token ends with '_').
  const updPrev = (p) => {
    if (p > tokStart) {
      const c = src[p - 1];
      if (c !== '_') prevChar = c;
    }
  };
  let searchPos = 0;
  for (;;) {
    reNextSpecial.lastIndex = searchPos;
    const m = reNextSpecial.exec(src);
    if (!m) break;
    const p = m.index;
    // The raw-block state that applies to the text run ending here is the
    // state BEFORE this position's construct is attempted (a <code> tag
    // flips it only for the text that follows it).
    const rawBefore = st.inRawBlock;
    const ch = src.charCodeAt(p);
    let res = null;
    let tried = false;
    if (ch === 92) {
      // backslash: escape, or a hard break before a newline
      updPrev(p);
      tried = true;
      res = tryEscape(src, p, mode) || tryBr(src, p, mode);
    } else if (ch === 60) {
      updPrev(p);
      tried = true;
      res = tryTag(src, p, st) || tryAutolink(src, p, mode);
    } else if (ch === 91 || ch === 33) {
      updPrev(p);
      tried = true;
      res = tryInlineLink(src, p, st, links, mode) || tryRefLink(src, p, st, links, mode);
    } else if (ch === 42 || ch === 95) {
      updPrev(p);
      tried = true;
      res = tryEmStrong(src, needMask(), closers, p, prevChar, st, links, mode);
    } else if (ch === 96) {
      updPrev(p);
      tried = true;
      res = tryCodeSpan(src, p, mode);
      if (!res) {
        // A failed code span leaves the whole backtick run as text;
        // marked never retries a span starting inside the run.
        let q = p;
        while (src.charCodeAt(q) === 96) q++;
        tokStart = q - 1;
        searchPos = q;
        continue;
      }
    } else if (ch === 32) {
      updPrev(p);
      tried = true;
      res = tryBr(src, p, mode);
    } else if (ch === 126) {
      updPrev(p);
      tried = true;
      res = tryDel(src, needMask(), closers, p, prevChar, st, links, mode);
      if (!res) {
        // A failed strikethrough leaves the whole tilde run as text.
        let q = p;
        while (src.charCodeAt(q) === 126) q++;
        tokStart = q - 1;
        searchPos = q;
        continue;
      }
    } else if (!st.inLink && isUrlStart(src, p, ch)) {
      updPrev(p);
      tried = true;
      res = tryUrl(src, p, mode);
    }
    if (res) {
      flushText(p, rawBefore);
      out.push(res.html);
      searchPos = p + res.len;
      textStart = searchPos;
      tokStart = searchPos;
      prevChar = '';
    } else {
      if (tried) tokStart = p;
      searchPos = p + 1;
    }
  }
  flushText(n, st.inRawBlock);
  return out.join('');
}

// ------------------------------------------------------------- block engine

function tokCode(src, pos) {
  reCode.lastIndex = pos;
  const m = reCode.exec(src);
  if (!m) return null;
  const raw = stripBlankTail(m[0]);
  const text = raw.replace(reCodeRemoveIndent, '');
  return { node: { k: 'code', raw, text, lang: '' }, next: pos + raw.length };
}

function fenceText(full, code) {
  const m = reIndentCodeComp.exec(full);
  if (!m) return code;
  const s = m[1];
  return code.split('\n').map((line) => {
    const o = reBeginningSpace.exec(line);
    if (!o) return line;
    return line.slice(Math.min(o[0].length, s.length));
  }).join('\n');
}

function tokFences(src, pos) {
  reFences.lastIndex = pos;
  const m = reFences.exec(src);
  if (!m) return null;
  const lang = m[2] ? m[2].trim().replace(reAnyPunct, '$1') : m[2];
  const text = fenceText(m[0], m[3] || '');
  return { node: { k: 'code', raw: m[0], text, lang }, next: pos + m[0].length };
}

function tokHeading(src, pos) {
  reHeading.lastIndex = pos;
  const m = reHeading.exec(src);
  if (!m) return null;
  let text = m[2].trim();
  if (reEndingHash.test(text)) {
    const s = rtrimCh(text, 35);
    if (!s || reEndingSpaceTab.test(s)) text = s.trim();
  }
  const raw = rtrimCh(m[0], 10);
  return { node: { k: 'heading', raw, depth: m[1].length, text }, next: pos + raw.length };
}

function tokHtml(src, pos) {
  reHtmlBlock.lastIndex = pos;
  const m = reHtmlBlock.exec(src);
  if (!m) return null;
  const raw = stripBlankTail(m[0]);
  const pre = m[1] === 'pre' || m[1] === 'script' || m[1] === 'style';
  return { node: { k: 'html', raw, text: raw, pre }, next: pos + raw.length };
}

function tokDef(src, pos) {
  reDef.lastIndex = pos;
  const m = reDef.exec(src);
  if (!m) return null;
  if (!reStartAngle.test(m[2]) && findClose(m[2], '()') !== -1) return null;
  const tag = normLabel(m[1]);
  const href = m[2] ? m[2].replace(reHrefBrackets, '$1').replace(reAnyPunct, '$1') : '';
  const title = m[3] ? m[3].substring(1, m[3].length - 1).replace(reAnyPunct, '$1') : m[3];
  const raw = rtrimCh(m[0], 10);
  return { node: { k: 'def', raw, tag, href, title }, next: pos + raw.length };
}

function tokTable(src, pos) {
  reTable.lastIndex = pos;
  const m = reTable.exec(src);
  if (!m || !reTableDelim.test(m[2])) return null;
  const headerCells = splitCells(m[1]);
  const delim = m[2].replace(reTableAlignChars, '').split('|');
  if (headerCells.length !== delim.length) return null;
  const raw = rtrimCh(m[0], 10);
  const node = { k: 'table', raw, header: [], align: [], rows: [] };
  for (const cell of delim) {
    if (reAlignRight.test(cell)) node.align.push('right');
    else if (reAlignCenter.test(cell)) node.align.push('center');
    else if (reAlignLeft.test(cell)) node.align.push('left');
    else node.align.push(null);
  }
  for (let i = 0; i < headerCells.length; i++) {
    node.header.push({ text: headerCells[i], align: node.align[i] });
  }
  const rowsRaw = m[3] && m[3].trim() ? m[3].replace(reTableRowBlank, '').split('\n') : [];
  for (const row of rowsRaw) {
    node.rows.push(splitCells(row, headerCells.length).map((c, p) => ({ text: c, align: node.align[p] })));
  }
  return { node, next: pos + raw.length };
}

function tokLheading(src, pos) {
  reSetextOrBlank.lastIndex = pos;
  const pre = reSetextOrBlank.exec(src);
  if (!pre) return null;
  const p0 = pre[0];
  let j = 1;
  while (p0.charCodeAt(j) === 32) j++;
  const pc = p0.charCodeAt(j);
  if (pc !== 61 && pc !== 45) return null; // a blank line came first
  reLheading.lastIndex = pos;
  const m = reLheading.exec(src);
  if (!m) return null;
  const raw = rtrimCh(m[0], 10);
  return {
    node: { k: 'heading', raw, depth: m[2].charAt(0) === '=' ? 1 : 2, text: m[1].trim() },
    next: pos + raw.length,
  };
}

function tokParagraph(src, pos) {
  reParagraphTop.lastIndex = pos;
  const m = reParagraphTop.exec(src);
  if (!m) return null;
  let text = m[1];
  if (text.charAt(text.length - 1) === '\n') text = text.slice(0, -1);
  return { node: { k: 'paragraph', raw: m[0], text }, next: pos + m[0].length };
}

function tokText(src, pos) {
  reText.lastIndex = pos;
  const m = reText.exec(src);
  if (!m) return null;
  return { node: { k: 'text', raw: m[0], text: m[0] }, next: pos + m[0].length };
}

// Blockquote tokenizing on a whole string (used for the nested re-parse).
function tokBlockquoteStr(s, links, lexState) {
  const r = tokBlockquote(s, 0, links, lexState);
  return r ? r.node : null;
}

function tokBlockquote(src, pos, links, lexState) {
  reBlockquote.lastIndex = pos;
  const m = reBlockquote.exec(src);
  if (!m) return null;
  let lines = rtrimCh(m[0], 10).split('\n');
  let rawAcc = '';
  let textAcc = '';
  const nodes = [];
  while (lines.length > 0) {
    let seen = false;
    const chunk = [];
    let p = 0;
    for (; p < lines.length; p++) {
      if (reBlockquoteStart.test(lines[p])) { chunk.push(lines[p]); seen = true; }
      else if (!seen) chunk.push(lines[p]);
      else break;
    }
    lines = lines.slice(p);
    const h = chunk.join('\n');
    const u = h
      .replace(reBlockquoteMarkerWs, (g, b, ws) => b + expandTabs(ws, b.length))
      .replace(reBlockquoteSetext, '\n    $1')
      .replace(reBlockquoteSetext2, '');
    rawAcc = rawAcc ? rawAcc + '\n' + h : h;
    textAcc = textAcc ? textAcc + '\n' + u : u;
    const savedTop = lexState.top;
    lexState.top = true;
    blockLexInto(u, links, lexState, true, nodes);
    lexState.top = savedTop;
    if (lines.length === 0) break;
    const k = nodes[nodes.length - 1];
    if (!k) break;
    if (k.k === 'code' || k.k === 'heading' || k.k === 'hr' || k.k === 'html' || k.k === 'table') break;
    if (k.k === 'blockquote') {
      const g = k;
      const b = lines.join('\n');
      const mm = g.raw + '\n' + b.replace(reBlockquoteSetext2, '');
      const f = tokBlockquoteStr(mm, links, lexState);
      nodes[nodes.length - 1] = f;
      const y = mm.substring(f.raw.length).replace(/^\n/, '');
      const R = y ? y.split('\n').length : 0;
      const A = R ? lines.slice(0, -R) : lines;
      if (A.length > 0) rawAcc += '\n' + A.join('\n');
      textAcc = textAcc.substring(0, textAcc.length - g.text.length) + f.text;
      lines = lines.slice(A.length);
      if (lines.length > 0 && reBlockquoteStart.test(lines[0])) continue;
      break;
    }
    if (k.k === 'list') {
      const g = k;
      const b = g.raw + '\n' + lines.join('\n');
      const mm = tokListStr(b, links, lexState);
      nodes[nodes.length - 1] = mm;
      const f = mm.raw.length > g.raw.length
        ? b.slice(g.raw.length + 1, mm.raw.length).split('\n').length
        : 0;
      if (f > 0) {
        const y = lines.slice(0, f).join('\n');
        rawAcc += '\n' + y;
        textAcc += '\n' + y;
      }
      lines = lines.slice(f);
      continue;
    }
    // Any other last token (paragraph, text, space, def): next chunk.
  }
  return { node: { k: 'blockquote', raw: rawAcc, text: textAcc, nodes }, next: pos + rawAcc.length };
}

function tokListStr(s, links, lexState) {
  const r = tokList(s, 0, links, lexState);
  return r ? r.node : null;
}

// First content character of a block-start pattern (fences, heading, html,
// blockquote, list bullet, hr) after up to three leading spaces; false if
// there is none (a leading tab blocks every block-start pattern).
function canBlockStart(s) {
  let i = 0;
  while (i < 3 && s.charCodeAt(i) === 32) i++;
  const c = s.charCodeAt(i);
  return c === 96 || c === 126 || c === 35 || c === 60 || c === 62 || c === 42 || c === 43 || c === 45 || c === 95 || (c >= 48 && c <= 57);
}

// Column of the first non-space character of s, counting each tab as four
// columns (as String.replace(/\t/g, '    ') does); -1 if s has none.
function expandedNonSpace(s) {
  let i = 0;
  let col = 0;
  while (i < s.length) {
    const c = s.charCodeAt(i);
    if (c === 32) { col++; i++; }
    else if (c === 9) { col += 4; i++; }
    else return col;
  }
  return -1;
}

// Manual equivalent of /\n[ \t]*\n[ \t]*$/ (a blank line at the end): scans
// only the trailing whitespace instead of running the regex engine.
function endsDoubleBlank(s) {
  let i = s.length;
  while (i > 0 && (s.charCodeAt(i - 1) === 32 || s.charCodeAt(i - 1) === 9)) i--;
  if (i === 0 || s.charCodeAt(i - 1) !== 10) return false;
  i--;
  while (i > 0 && (s.charCodeAt(i - 1) === 32 || s.charCodeAt(i - 1) === 9)) i--;
  return i > 0 && s.charCodeAt(i - 1) === 10;
}

function tokList(src, pos, links, lexState) {
  reList.lastIndex = pos;
  const t = reList.exec(src);
  if (!t) return null;
  const bulletRaw = t[1].trim();
  const ordered = bulletRaw.length > 1;
  const node = {
    k: 'list', raw: '', ordered,
    start: ordered ? +bulletRaw.slice(0, -1) : '',
    loose: false, items: [],
  };
  const bulletPat = ordered ? `\\d{1,9}\\${bulletRaw.slice(-1)}` : `\\${bulletRaw}`;
  const itemRe = listItemRe(bulletPat);
  const startPos = pos;
  const len = src.length;
  const lineEnd = (i) => {
    const j = src.indexOf('\n', i);
    return j === -1 ? len : j;
  };
  let cur = pos;
  let p = false;
  while (cur < len) {
    let u = false;
    const dParts = [];
    itemRe.lastIndex = cur;
    const it = itemRe.exec(src);
    if (!it) break;
    reHr.lastIndex = cur;
    if (reHr.exec(src)) break;
    const itemStart = cur;
    cur += it[0].length;
    const g = (() => { const nl = it[2].indexOf('\n'); return nl === -1 ? it[2] : it[2].slice(0, nl); })();
    const b = it[1].length;
    let m = g.replace(reLeadingSpaceTab, (v) => expandTabs(v, b));
    const f0 = src.slice(cur, lineEnd(cur));
    const y0 = !m.trim();
    let R = 0;
    if (y0) {
      R = b + 1;
      dParts.push('');
    } else {
      R = m.search(reNonSpace);
      if (R > 4) R = 1;
      dParts.push(m.slice(R));
      R += b;
    }
    let y = y0;
    if (y && reBlankLine.test(f0)) {
      cur += f0.length + 1;
      u = true;
    }
    if (!u) {
      const res = indentRes(R);
      while (cur < len) {
        const le = src.indexOf('\n', cur);
        const le2 = le === -1 ? len : le;
        // Scan the leading whitespace directly in src: i is the offset of
        // the first non-space character, col its tab-expanded column, pre
        // the tab-expanded leading whitespace, ind is col (-1 for a blank
        // line), c2 the first non-space character.
        let i = 0;
        let col = 0;
        let pre = '';
        while (cur + i < le2) {
          const c = src.charCodeAt(cur + i);
          if (c === 32) { col++; pre += ' '; i++; }
          else if (c === 9) { const r = 4 - (col % 4); col += r; pre += '    '.slice(0, r); i++; }
          else break;
        }
        const ind = cur + i < le2 ? col : -1;
        const c2 = src.charCodeAt(cur + i);
        // The block-start tests below all begin with ` {0,3}`, so they
        // cannot match a line whose first non-space character sits at
        // column 4 or later, or a blank line; and every block-start
        // pattern begins with one of the characters in the set, so the
        // six regexes are skipped unless it matches.
        if (ind >= 0 && ind < 4 && (c2 === 96 || c2 === 126 || c2 === 35 || c2 === 60 || c2 === 62 || c2 === 42 || c2 === 43 || c2 === 45 || c2 === 95 || (c2 >= 48 && c2 <= 57))) {
          const f = src.slice(cur, le2);
          if (
            res.fences.test(f) || res.heading.test(f) || res.html.test(f) ||
            res.blockquote.test(f) || res.nextBullet.test(f) || res.hr.test(f)
          ) break;
        }
        // The dedented line (the tab-expanded line with its first R
        // columns removed): Z is pre + the rest of the line.
        let zs;
        if (R <= pre.length) zs = pre.slice(R) + src.slice(cur + i, le2);
        else zs = src.slice(cur + i + (R - pre.length), le2);
        if (ind >= R || ind === -1) {
          dParts.push(zs);
        } else {
          if (
            y || expandedNonSpace(m) >= 4 ||
            (canBlockStart(m) && (res.fences.test(m) || res.heading.test(m) || res.html.test(m) || res.hr.test(m)))
          ) break;
          let qe;
          const f = src.slice(cur, le2);
          if ((c2 === 61 || c2 === 45) && reSetextLine.test(f) && reLheadingTest.test(m + '\n' + f)) {
            qe = '    ' + pre.slice(Math.min(3, pre.length)) + src.slice(cur + i, le2);
          } else {
            qe = f;
          }
          dParts.push(qe);
        }
        y = ind === -1;
        cur = le2 + 1;
        m = zs;
      }
    }
    const d = dParts.join('\n');
    const A = src.slice(itemStart, cur);
    if (!node.loose) {
      if (p) node.loose = true;
      else if (endsDoubleBlank(A)) p = true;
    }
    node.items.push({
      raw: A, task: reListIsTask.test(d), loose: false, text: d, nodes: [],
    });
  }
  const last = node.items[node.items.length - 1];
  if (!last) return null;
  last.raw = last.raw.trimEnd();
  last.text = last.text.trimEnd();
  node.raw = src.slice(startPos, cur).trimEnd();
  for (const item of node.items) {
    lexState.top = false;
    item.nodes = blockLex(item.text, links, lexState, false);
    if (!node.loose) {
      const spaces = item.nodes.filter((g) => g.k === 'space');
      if (spaces.length > 0 && spaces.some((g) => reAnyLine.test(g.raw))) node.loose = true;
    }
  }
  for (const item of node.items) {
    const first = item.nodes[0];
    if (item.task && first && (first.k === 'text' || first.k === 'paragraph')) {
      item.text = item.text.replace(reListReplaceTask, '');
      first.raw = first.raw.replace(reListReplaceTask, '');
      first.text = first.text.replace(reListReplaceTask, '');
      const ck = reListTaskCheckbox.exec(item.raw);
      if (ck) {
        const cb = { checked: ck[0] !== '[ ]' };
        item.checked = cb.checked;
        if (node.loose) {
          first.cb = cb;
        } else {
          item.cbBlock = cb;
        }
      }
    } else if (item.task) {
      item.task = false;
    }
  }
  if (node.loose) {
    for (const item of node.items) {
      item.loose = true;
      for (const tok of item.nodes) {
        if (tok.k === 'text') tok.k = 'paragraph';
      }
    }
  }
  return { node, next: startPos + node.raw.length };
}

function blockLex(src, links, lexState, nested) {
  const nodes = [];
  blockLexInto(src, links, lexState, nested, nodes);
  return nodes;
}

// Tries the block tokenizers that need a specific first character
// (indented code, fences, heading, hr, blockquote, list, html, link
// definition). Returns the next position, or -1 when none matched.
function tryBlockStart(src, pos, links, lexState, nodes) {
  let r = tokCode(src, pos);
  if (r) {
    const prev = nodes[nodes.length - 1];
    if (prev && (prev.k === 'paragraph' || prev.k === 'text')) {
      prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + r.node.raw;
      prev.text += '\n' + r.node.text;
    } else {
      nodes.push(r.node);
    }
    return r.next;
  }
  r = tokFences(src, pos);
  if (r) { nodes.push(r.node); return r.next; }
  r = tokHeading(src, pos);
  if (r) { nodes.push(r.node); return r.next; }
  reHr.lastIndex = pos;
  const hm = reHr.exec(src);
  if (hm) {
    const raw = rtrimCh(hm[0], 10);
    nodes.push({ k: 'hr', raw });
    return pos + raw.length;
  }
  r = tokBlockquote(src, pos, links, lexState);
  if (r) { nodes.push(r.node); return r.next; }
  r = tokList(src, pos, links, lexState);
  if (r) { nodes.push(r.node); return r.next; }
  r = tokHtml(src, pos);
  if (r) { nodes.push(r.node); return r.next; }
  r = tokDef(src, pos);
  if (r) {
    const prev = nodes[nodes.length - 1];
    if (prev && (prev.k === 'paragraph' || prev.k === 'text')) {
      prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + r.node.raw;
      prev.text += '\n' + r.node.raw;
    } else {
      if (!Object.hasOwn(links, r.node.tag)) {
        links[r.node.tag] = { href: r.node.href, title: r.node.title };
      }
      nodes.push(r.node);
    }
    return r.next;
  }
  return -1;
}

function blockLexInto(src, links, lexState, nested, nodes) {
  const len = src.length;
  let pos = 0;
  let lastLen = Infinity;
  let nestedFlag = nested;
  while (pos < len) {
    const rem = len - pos;
    if (rem >= lastLen) throw new Error('Infinite loop on byte: ' + src.charCodeAt(pos));
    lastLen = rem;
    reSpace.lastIndex = pos;
    const sm = reSpace.exec(src);
    if (sm && sm[0].length > 0) {
      const raw = sm[0];
      const prev = nodes[nodes.length - 1];
      if (raw.length === 1 && prev) prev.raw += '\n';
      else nodes.push({ k: 'space', raw });
      pos += raw.length;
      continue;
    }
    const fc = src.charCodeAt(pos);
    if (fc === 9 || fc === 32 || fc === 96 || fc === 126 || fc === 35 || fc === 45 || fc === 95 || fc === 42 || fc === 43 || fc === 62 || fc === 60 || fc === 91 || (fc >= 48 && fc <= 57)) {
      const nx = tryBlockStart(src, pos, links, lexState, nodes);
      if (nx !== -1) { pos = nx; continue; }
    }
    let r;
    r = tokTable(src, pos, links);
    if (r) { nodes.push(r.node); pos = r.next; continue; }
    r = tokLheading(src, pos);
    if (r) { nodes.push(r.node); pos = r.next; continue; }
    if (lexState.top) {
      r = tokParagraph(src, pos);
      if (r) {
        const prev = nodes[nodes.length - 1];
        if (nestedFlag && prev && prev.k === 'paragraph') {
          prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + r.node.raw;
          prev.text += '\n' + r.node.text;
        } else {
          nodes.push(r.node);
        }
        nestedFlag = false;
        pos = r.next;
        continue;
      }
    }
    r = tokText(src, pos);
    if (r) {
      const prev = nodes[nodes.length - 1];
      if (prev && prev.k === 'text') {
        prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + r.node.raw;
        prev.text += '\n' + r.node.text;
      } else {
        nodes.push(r.node);
      }
      pos = r.next;
      continue;
    }
    throw new Error('Infinite loop on byte: ' + src.charCodeAt(pos));
  }
  lexState.top = true;
  return nodes;
}

// --------------------------------------------------------------- rendering

const reLheadingTest = rx(LHEADING_SRC, '');

function checkboxHtml(checked) {
  return '<input ' + (checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
}

// A top-level inline unit: the raw-block state resets before each one.
function topInline(text, links, st, mode) {
  st.inRawBlock = false;
  return inlineHTML(text, links, st, mode);
}

function renderCell(cell, header, links, st) {
  const inner = topInline(cell.text, links, st, 0);
  const tag = header ? 'th' : 'td';
  const open = cell.align ? `<${tag} align="${cell.align}">` : `<${tag}>`;
  return open + inner + `</${tag}>\n`;
}

function renderBlocks(nodes, links, st) {
  let out = '';
  for (const node of nodes) out += renderBlock(node, links, st);
  return out;
}

function renderBlock(node, links, st) {
  switch (node.k) {
    case 'space':
      return '';
    case 'hr':
      return '<hr>\n';
    case 'heading': {
      const inner = topInline(node.text, links, st, 0);
      return `<h${node.depth}>${inner}</h${node.depth}>\n`;
    }
    case 'code': {
      const lang = (node.lang || '').match(reNotSpaceStart)?.[0] || '';
      const text = node.text ? node.text.replace(reEndingNewline, '') + '\n' : '';
      const body = esc(text, true);
      return lang
        ? `<pre><code class="language-${esc(lang)}">${body}</code></pre>\n`
        : `<pre><code>${body}</code></pre>\n`;
    }
    case 'blockquote':
      return `<blockquote>\n${renderBlocks(node.nodes, links, st)}</blockquote>\n`;
    case 'html':
      return node.text;
    case 'def':
      return '';
    case 'paragraph': {
      if (node.cbOnly) return `<p>${checkboxHtml(node.cb.checked)}</p>\n`;
      const cb = node.cb ? checkboxHtml(node.cb.checked) : '';
      return `<p>${cb}${topInline(node.text, links, st, 0)}</p>\n`;
    }
    case 'text': {
      const cb = node.cb ? checkboxHtml(node.cb.checked) : '';
      return cb + topInline(node.text, links, st, 0);
    }
    case 'list': {
      const tag = node.ordered ? 'ol' : 'ul';
      const startAttr = node.ordered && node.start !== 1 ? ` start="${node.start}"` : '';
      let items = '';
      for (const item of node.items) {
        const cb = item.cbBlock ? checkboxHtml(item.cbBlock.checked) : '';
        items += `<li>${cb}${renderBlocks(item.nodes, links, st)}</li>\n`;
      }
      return `<${tag}${startAttr}>\n${items}</${tag}>\n`;
    }
    case 'table': {
      let headCells = '';
      for (const c of node.header) headCells += renderCell(c, true, links, st);
      let body = '';
      for (const row of node.rows) {
        let cells = '';
        for (const c of row) cells += renderCell(c, false, links, st);
        body += `<tr>\n${cells}</tr>\n`;
      }
      if (body) body = `<tbody>${body}</tbody>`;
      return `<table>\n<thead>\n<tr>\n${headCells}</tr>\n</thead>\n${body}</table>\n`;
    }
    default:
      throw new Error('Token with "' + node.k + '" type was not found.');
  }
}

/** The HTML marked 18.1.3 renders for `markdown`, with marked's defaults. */
export function parse(markdown) {
  // Most inputs hold no carriage return at all; skip the normalization
  // scan entirely for them (identical result: replace is a no-op then).
  const src = markdown.includes('\r') ? markdown.replace(/\r\n|\r/g, '\n') : markdown;
  const links = Object.create(null);
  const lexState = { top: true };
  const nodes = blockLex(src, links, lexState, false);
  const st = { inLink: false, inRawBlock: false, linkEmitted: false, parenPossible: true, hasLinks: Object.keys(links).length > 0 };
  return renderBlocks(nodes, links, st);
}
