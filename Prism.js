(function() {
  const CRC_TABLE = (() => {
    const t = new Uint32Array(256);
    for (let n = 0; n < 256; n++) {
      let c = n;
      for (let k = 0; k < 8; k++) c = c & 1 ? 3988292384 ^ c >>> 1 : c >>> 1;
      t[n] = c >>> 0;
    }
    return t;
  })();
  function crc32(bytes) {
    let c = 4294967295;
    for (let i = 0; i < bytes.length; i++) c = CRC_TABLE[(c ^ bytes[i]) & 255] ^ c >>> 8;
    return (c ^ 4294967295) >>> 0;
  }
  function novaInflateRaw(input, expectedLength) {
    let pos = 0, bitBuf = 0, bitCount = 0;
    function getBit() {
      if (bitCount === 0) {
        bitBuf = input[pos++];
        bitCount = 8;
      }
      const bit = bitBuf & 1;
      bitBuf >>>= 1;
      bitCount--;
      return bit;
    }
    function getBits(n) {
      let val = 0;
      for (let i = 0; i < n; i++) val |= getBit() << i;
      return val >>> 0;
    }
    function buildTree(lengths) {
      const MAXBITS = 15;
      const counts = new Array(MAXBITS + 1).fill(0);
      for (const l of lengths) counts[l]++;
      counts[0] = 0;
      const offsets = new Array(MAXBITS + 2).fill(0);
      for (let i = 1; i <= MAXBITS; i++) offsets[i + 1] = offsets[i] + counts[i];
      const symbols = new Array(lengths.length).fill(0);
      for (let i = 0; i < lengths.length; i++) if (lengths[i]) symbols[offsets[lengths[i]]++] = i;
      return {
        counts: counts,
        symbols: symbols
      };
    }
    function decodeSymbol(tree) {
      let code = 0, first = 0, index = 0;
      for (let len = 1; len <= 15; len++) {
        code |= getBit();
        const count = tree.counts[len];
        if (code - first < count) return tree.symbols[index + (code - first)];
        index += count;
        first += count;
        first <<= 1;
        code <<= 1;
      }
      throw new Error("inflate: bad code");
    }
    const LEN_BASE = [ 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258 ];
    const LEN_EXTRA = [ 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0 ];
    const DIST_BASE = [ 1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577 ];
    const DIST_EXTRA = [ 0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13 ];
    const CLC_ORDER = [ 16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15 ];
    let fixedLitTree, fixedDistTree;
    function getFixedTrees() {
      if (fixedLitTree) return [ fixedLitTree, fixedDistTree ];
      const litLengths = new Array(288);
      let i = 0;
      for (;i < 144; i++) litLengths[i] = 8;
      for (;i < 256; i++) litLengths[i] = 9;
      for (;i < 280; i++) litLengths[i] = 7;
      for (;i < 288; i++) litLengths[i] = 8;
      const distLengths = new Array(30).fill(5);
      fixedLitTree = buildTree(litLengths);
      fixedDistTree = buildTree(distLengths);
      return [ fixedLitTree, fixedDistTree ];
    }
    const out = new Uint8Array(expectedLength);
    let outPos = 0;
    function pushByte(b) {
      out[outPos++] = b;
    }
    let final = false;
    while (!final) {
      final = getBit() === 1;
      const type = getBits(2);
      if (type === 0) {
        bitBuf = 0;
        bitCount = 0;
        const len = input[pos] | input[pos + 1] << 8;
        pos += 4;
        for (let i = 0; i < len; i++) pushByte(input[pos++]);
      } else {
        let litTree, distTree;
        if (type === 1) {
          [litTree, distTree] = getFixedTrees();
        } else if (type === 2) {
          const hlit = getBits(5) + 257;
          const hdist = getBits(5) + 1;
          const hclen = getBits(4) + 4;
          const clcLengths = new Array(19).fill(0);
          for (let i = 0; i < hclen; i++) clcLengths[CLC_ORDER[i]] = getBits(3);
          const clcTree = buildTree(clcLengths);
          const lengths = [];
          while (lengths.length < hlit + hdist) {
            const sym = decodeSymbol(clcTree);
            if (sym < 16) lengths.push(sym); else if (sym === 16) {
              const rep = getBits(2) + 3;
              const prev = lengths[lengths.length - 1];
              for (let i = 0; i < rep; i++) lengths.push(prev);
            } else if (sym === 17) {
              const rep = getBits(3) + 3;
              for (let i = 0; i < rep; i++) lengths.push(0);
            } else {
              const rep = getBits(7) + 11;
              for (let i = 0; i < rep; i++) lengths.push(0);
            }
          }
          litTree = buildTree(lengths.slice(0, hlit));
          distTree = buildTree(lengths.slice(hlit));
        } else {
          throw new Error("inflate: bad block type " + type);
        }
        while (true) {
          const sym = decodeSymbol(litTree);
          if (sym < 256) pushByte(sym); else if (sym === 256) break; else {
            const li = sym - 257;
            const len = LEN_BASE[li] + getBits(LEN_EXTRA[li]);
            const dsym = decodeSymbol(distTree);
            const dist = DIST_BASE[dsym] + getBits(DIST_EXTRA[dsym]);
            const from = outPos - dist;
            for (let i = 0; i < len; i++) pushByte(out[from + i]);
          }
        }
      }
    }
    return out;
  }
  function dosDateTime(date) {
    const time = (date.getHours() & 31) << 11 | (date.getMinutes() & 63) << 5 | date.getSeconds() >> 1 & 31;
    const dosDate = (date.getFullYear() - 1980 & 127) << 9 | (date.getMonth() + 1 & 15) << 5 | date.getDate() & 31;
    return {
      time: time,
      dosDate: dosDate
    };
  }
  function writeUint32LE(arr, offset, val) {
    arr[offset] = val & 255;
    arr[offset + 1] = val >>> 8 & 255;
    arr[offset + 2] = val >>> 16 & 255;
    arr[offset + 3] = val >>> 24 & 255;
  }
  function writeUint16LE(arr, offset, val) {
    arr[offset] = val & 255;
    arr[offset + 1] = val >>> 8 & 255;
  }
  function buildZip(entries) {
    const {time: time, dosDate: dosDate} = dosDateTime(new Date);
    const parts = [];
    const centralParts = [];
    let offset = 0;
    for (const entry of entries) {
      const nameBytes = (new TextEncoder).encode(entry.name);
      const data = entry.data || new Uint8Array(0);
      const crc = entry.isDir ? 0 : crc32(data);
      const size = entry.isDir ? 0 : data.length;
      const localHeader = new Uint8Array(30 + nameBytes.length);
      writeUint32LE(localHeader, 0, 67324752);
      writeUint16LE(localHeader, 4, 20);
      writeUint16LE(localHeader, 6, 0);
      writeUint16LE(localHeader, 8, 0);
      writeUint16LE(localHeader, 10, time);
      writeUint16LE(localHeader, 12, dosDate);
      writeUint32LE(localHeader, 14, crc);
      writeUint32LE(localHeader, 18, size);
      writeUint32LE(localHeader, 22, size);
      writeUint16LE(localHeader, 26, nameBytes.length);
      writeUint16LE(localHeader, 28, 0);
      localHeader.set(nameBytes, 30);
      parts.push(localHeader);
      if (!entry.isDir) parts.push(data);
      const centralHeader = new Uint8Array(46 + nameBytes.length);
      writeUint32LE(centralHeader, 0, 33639248);
      writeUint16LE(centralHeader, 4, 20);
      writeUint16LE(centralHeader, 6, 20);
      writeUint16LE(centralHeader, 8, 0);
      writeUint16LE(centralHeader, 10, 0);
      writeUint16LE(centralHeader, 12, time);
      writeUint16LE(centralHeader, 14, dosDate);
      writeUint32LE(centralHeader, 16, crc);
      writeUint32LE(centralHeader, 20, size);
      writeUint32LE(centralHeader, 24, size);
      writeUint16LE(centralHeader, 28, nameBytes.length);
      writeUint16LE(centralHeader, 30, 0);
      writeUint16LE(centralHeader, 32, 0);
      writeUint16LE(centralHeader, 34, 0);
      writeUint16LE(centralHeader, 36, 0);
      writeUint32LE(centralHeader, 38, entry.isDir ? 16 : 0);
      writeUint32LE(centralHeader, 42, offset);
      centralHeader.set(nameBytes, 46);
      centralParts.push(centralHeader);
      offset += localHeader.length + (entry.isDir ? 0 : data.length);
    }
    const centralStart = offset;
    let centralSize = 0;
    for (const p of centralParts) centralSize += p.length;
    const eocd = new Uint8Array(22);
    writeUint32LE(eocd, 0, 101010256);
    writeUint16LE(eocd, 4, 0);
    writeUint16LE(eocd, 6, 0);
    writeUint16LE(eocd, 8, entries.length);
    writeUint16LE(eocd, 10, entries.length);
    writeUint32LE(eocd, 12, centralSize);
    writeUint32LE(eocd, 16, centralStart);
    writeUint16LE(eocd, 20, 0);
    return [ ...parts, ...centralParts, eocd ];
  }
  function readUint32LE(view, offset) {
    return view.getUint32(offset, true);
  }
  function readUint16LE(view, offset) {
    return view.getUint16(offset, true);
  }
  function parseZip(bytes) {
    const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
    let eocdOffset = -1;
    for (let i = bytes.length - 22; i >= 0 && i >= bytes.length - 22 - 65536; i--) {
      if (readUint32LE(view, i) === 101010256) {
        eocdOffset = i;
        break;
      }
    }
    if (eocdOffset === -1) throw new Error("Not a valid zip file (no end-of-central-directory record found).");
    const entryCount = readUint16LE(view, eocdOffset + 10);
    const centralDirOffset = readUint32LE(view, eocdOffset + 16);
    const files = {};
    let p = centralDirOffset;
    for (let i = 0; i < entryCount; i++) {
      if (readUint32LE(view, p) !== 33639248) throw new Error("Corrupt zip central directory.");
      const method = readUint16LE(view, p + 10);
      const compSize = readUint32LE(view, p + 20);
      const uncompSize = readUint32LE(view, p + 24);
      const nameLen = readUint16LE(view, p + 28);
      const extraLen = readUint16LE(view, p + 30);
      const commentLen = readUint16LE(view, p + 32);
      const externalAttrs = readUint32LE(view, p + 38);
      const localHeaderOffset = readUint32LE(view, p + 42);
      const name = (new TextDecoder).decode(bytes.subarray(p + 46, p + 46 + nameLen));
      const isDir = name.endsWith("/") || (externalAttrs & 16) !== 0;
      files[name] = {
        name: name,
        dir: isDir,
        async async(type) {
          let out;
          if (isDir) {
            out = new Uint8Array(0);
          } else {
            const lp = localHeaderOffset;
            if (readUint32LE(view, lp) !== 67324752) throw new Error("Corrupt zip local header for " + name);
            const lNameLen = readUint16LE(view, lp + 26);
            const lExtraLen = readUint16LE(view, lp + 28);
            const dataStart = lp + 30 + lNameLen + lExtraLen;
            const compBytes = bytes.subarray(dataStart, dataStart + compSize);
            out = method === 0 ? compBytes : novaInflateRaw(compBytes, uncompSize);
          }
          if (type === "string") return (new TextDecoder).decode(out);
          if (type === "blob") return new Blob([ out ]);
          return out;
        }
      };
      p += 46 + nameLen + extraLen + commentLen;
    }
    return {
      files: files,
      file(path) {
        return files[path];
      }
    };
  }
  async function toUint8Array(data) {
    if (data == null) return new Uint8Array(0);
    if (typeof data === "string") return (new TextEncoder).encode(data);
    if (data instanceof Uint8Array) return data;
    if (data instanceof ArrayBuffer) return new Uint8Array(data);
    if (typeof Blob !== "undefined" && data instanceof Blob) return new Uint8Array(await data.arrayBuffer());
    if (data && typeof data.arrayBuffer === "function") return new Uint8Array(await data.arrayBuffer());
    throw new Error("Unsupported zip entry data type.");
  }
  class NovaZipWriter {
    constructor() {
      this._entries = [];
    }
    file(name, data) {
      this._entries.push({
        name: name,
        data: data,
        isDir: false
      });
      return this;
    }
    folder(name) {
      return name;
    }
    async generateAsync(opts) {
      const resolved = [];
      for (const e of this._entries) resolved.push({
        name: e.name,
        data: await toUint8Array(e.data),
        isDir: e.isDir
      });
      const parts = buildZip(resolved);
      if (opts && opts.type === "uint8array") {
        let total = 0;
        for (const part of parts) total += part.length;
        const out = new Uint8Array(total);
        let o = 0;
        for (const part of parts) {
          out.set(part, o);
          o += part.length;
        }
        return out;
      }
      return new Blob(parts, {
        type: "application/zip"
      });
    }
  }
  async function loadAsync(input) {
    const bytes = await toUint8Array(input);
    return parseZip(bytes);
  }
  function JSZip() {
    return new NovaZipWriter;
  }
  JSZip.loadAsync = loadAsync;
  window.JSZip = JSZip;
})();

let novaConfig = null;

const NOVA_DEFAULT_CONFIG = {
  appName: "Prism",
  configVersion: 1,
  terminals: [ {
    key: "music",
    label: "Music Terminal",
    icon: "🎵",
    mediaKind: "audio",
    dbStore: "music",
    hasPlaylists: true,
    hasHistory: true,
    extensions: [ "mp3", "wav", "ogg", "oga", "m4a", "aac", "flac", "weba", "opus" ]
  }, {
    key: "podcast",
    label: "Podcast Terminal",
    icon: "🎙️",
    mediaKind: "audio",
    dbStore: "podcast",
    hasPlaylists: true,
    hasHistory: true,
    extensions: [ "mp3", "wav", "m4a", "aac" ]
  }, {
    key: "video",
    label: "Video Terminal",
    icon: "🎬",
    mediaKind: "video",
    dbStore: "video",
    hasPlaylists: true,
    hasHistory: true,
    extensions: [ "mp4", "webm", "mkv", "mov" ]
  }, {
    key: "documentary",
    label: "Documentary Terminal",
    icon: "🎞️",
    mediaKind: "video",
    dbStore: "documentary",
    hasPlaylists: true,
    hasHistory: false,
    extensions: [ "mp4", "webm", "mkv" ]
  }, {
    key: "movie",
    label: "Movie Terminal",
    icon: "🍿",
    mediaKind: "video",
    dbStore: "movie",
    hasPlaylists: true,
    hasHistory: false,
    extensions: [ "mp4", "webm", "mkv" ]
  }, {
    key: "comedy",
    label: "Comedy Terminal",
    icon: "😂",
    mediaKind: "video",
    dbStore: "comedy",
    hasPlaylists: true,
    hasHistory: false,
    extensions: [ "mp4", "webm", "mkv" ]
  }, {
    key: "webseries",
    label: "Web Series Terminal",
    icon: "📺",
    mediaKind: "video",
    dbStore: "webseries",
    hasPlaylists: true,
    hasHistory: false,
    extensions: [ "mp4", "webm", "mkv" ]
  }, {
    key: "games",
    label: "Games Terminal",
    icon: "🎮",
    mediaKind: "file",
    dbStore: "games",
    hasPlaylists: false,
    hasHistory: false,
    extensions: [ "zip", "exe", "apk" ]
  }, {
    key: "books",
    label: "Book Terminal",
    icon: "📚",
    mediaKind: "text",
    dbStore: "books",
    hasPlaylists: false,
    hasHistory: false,
    extensions: [ "pdf", "epub", "txt" ]
  }, {
    key: "gamevideo",
    label: "Game Video Terminal",
    icon: "🕹️",
    mediaKind: "video",
    dbStore: "gamevideo",
    hasPlaylists: true,
    hasHistory: false,
    extensions: [ "mp4", "webm", "mkv" ]
  }, {
    key: "gamemovie",
    label: "Game Movie Terminal",
    icon: "🎥",
    mediaKind: "video",
    dbStore: "gamemovie",
    hasPlaylists: true,
    hasHistory: false,
    extensions: [ "mp4", "webm", "mkv" ]
  }, {
    key: "bookvideo",
    label: "Book Video Terminal",
    icon: "📖",
    mediaKind: "video",
    dbStore: "bookvideo",
    hasPlaylists: true,
    hasHistory: false,
    extensions: [ "mp4", "webm", "mkv" ]
  }, {
    key: "bookmovie",
    label: "Book Movie Terminal",
    icon: "🎦",
    mediaKind: "video",
    dbStore: "bookmovie",
    hasPlaylists: true,
    hasHistory: false,
    extensions: [ "mp4", "webm", "mkv" ]
  }, {
    key: "presentations",
    label: "Presentations Terminal",
    icon: "📽️",
    mediaKind: "file",
    dbStore: "presentations",
    hasPlaylists: false,
    hasHistory: false,
    extensions: [ "pdf", "pptx", "key" ]
  }, {
    key: "bookmark",
    label: "Bookmark Terminal",
    icon: "🔖",
    mediaKind: "link",
    dbStore: "bookmark",
    hasPlaylists: true,
    hasHistory: true,
    extensions: []
  } ],
  auth: {
    minUsernameLength: 3,
    minPasswordLength: 6,
    maxLoginAttempts: 5,
    lockoutMinutes: 5,
    passwordPromptAtAttempt: 3
  },
  recoveryPasskey: {
    min: 0,
    max: 1e12
  },
  search: {
    debounceMs: 150
  },
  storage: {
    quotaWarningPercent: 85
  },
  performance: {
    useUserIdIndex: true,
    renderBatching: "documentFragment",
    virtualizeListsAbove: 500,
    rowWindowSize: 60
  },
  securityQuestions: {
    requiredCorrectAnswers: 2,
    questionBank: [ "What is your favorite movie?", "What is your favorite food?", "What was the name of your first pet?", "What city were you born in?", "What is your favorite song?", "What was your childhood nickname?", "What is the name of your favorite book?", "What was the make of your first car?" ]
  },
  accountEvents: {
    types: [ "account_created", "login", "logout", "password_changed", "password_reset", "security_questions_set", "security_reset_used", "username_changed", "email_changed" ]
  },
  exportSchemas: {
    accountBackup: {
      version: 1,
      fields: [ "version", "exportedAt", "user", "playlists", "positions", "settings" ]
    },
    playlistShare: {
      version: 1,
      fields: [ "version", "terminalKey", "playlistName", "tracks" ]
    },
    accountActivityReport: {
      version: 1,
      fields: [ "userId", "generatedAt", "totals", "events" ]
    }
  }
};

async function loadNovaConfig() {
  novaConfig = NOVA_DEFAULT_CONFIG;
  return novaConfig;
}

function formatTime(t) {
  if (!t || !isFinite(t)) return "0:00";
  const m = Math.floor(t / 60);
  const s = Math.floor(t % 60);
  return `${m}:${s < 10 ? "0" + s : s}`;
}

function shuffleArray(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [ arr[j], arr[i] ];
  }
}

const LIST_SORT_STORAGE_PREFIX = "listSortMode:";

function saveListSortMode(type, mode, arr) {
  const payload = {
    mode: mode
  };
  if (mode === "shuffle") payload.order = arr.map(item => item.id);
  appSet(`${LIST_SORT_STORAGE_PREFIX}${type}`, payload);
}

function restoreListSortMode(type, arr) {
  const saved = appGet(`${LIST_SORT_STORAGE_PREFIX}${type}`, null);
  if (!saved || !saved.mode || !arr.length) return;
  if (saved.mode === "az") {
    arr.sort((a, b) => a.name.localeCompare(b.name));
  } else if (saved.mode === "za") {
    arr.sort((a, b) => b.name.localeCompare(a.name));
  } else if (saved.mode === "shuffle" && Array.isArray(saved.order)) {
    const byId = new Map(arr.map(item => [ item.id, item ]));
    const ordered = [];
    saved.order.forEach(id => {
      if (byId.has(id)) {
        ordered.push(byId.get(id));
        byId.delete(id);
      }
    });
    byId.forEach(item => ordered.push(item));
    arr.length = 0;
    arr.push(...ordered);
  }
}

function debounce(fn, delay = 150) {
  let timer = null;
  return (...args) => {
    clearTimeout(timer);
    timer = setTimeout(() => fn(...args), delay);
  };
}

function attachVisibilityToggle(inputEl, toggleBtnEl) {
  if (!inputEl || !toggleBtnEl) return;
  toggleBtnEl.setAttribute("aria-label", "Show");
  toggleBtnEl.textContent = "👁️";
  toggleBtnEl.addEventListener("click", () => {
    if (inputEl.tagName === "INPUT" && (inputEl.type === "password" || inputEl.type === "text")) {
      const willShow = inputEl.type === "password";
      inputEl.type = willShow ? "text" : "password";
      toggleBtnEl.textContent = willShow ? "🙈" : "👁️";
      toggleBtnEl.setAttribute("aria-label", willShow ? "Hide" : "Show");
    } else {
      const willShow = inputEl.dataset.masked !== "false";
      if (inputEl.dataset.realValue === undefined) inputEl.dataset.realValue = inputEl.textContent;
      inputEl.textContent = willShow ? inputEl.dataset.realValue : "•".repeat(Math.max(4, inputEl.dataset.realValue.length));
      inputEl.dataset.masked = willShow ? "false" : "true";
      toggleBtnEl.textContent = willShow ? "🙈" : "👁️";
      toggleBtnEl.setAttribute("aria-label", willShow ? "Hide" : "Show");
    }
  });
}

const miniPlayerRegistry = [];

function registerMiniPlayer(key, offFn, isOnFn) {
  miniPlayerRegistry.push({
    key: key,
    offFn: offFn,
    isOnFn: isOnFn
  });
}

function turnOffOtherMinis(exceptKey) {
  miniPlayerRegistry.forEach(m => {
    if (m.key !== exceptKey && m.isOnFn()) m.offFn();
  });
}

const ZIP_EXTENSIONS_BY_TYPE = {
  audio: [ "mp3", "wav", "ogg", "oga", "m4a", "aac", "flac", "weba", "opus" ],
  video: [ "mp4", "webm", "mkv", "mov", "avi", "m4v", "ogv" ],
  pdf: [ "pdf" ],
  presentation: [ "pdf", "ppt", "pptx" ],
  game: [ "html", "htm", "css", "js" ]
};

const PLAYLIST_FOLDER_IMPORT_HANDLERS = {};

function guessMimeTypeFromName(name) {
  const ext = (name.split(".").pop() || "").toLowerCase();
  const map = {
    mp3: "audio/mpeg",
    wav: "audio/wav",
    ogg: "audio/ogg",
    oga: "audio/ogg",
    m4a: "audio/mp4",
    aac: "audio/aac",
    flac: "audio/flac",
    weba: "audio/webm",
    opus: "audio/ogg",
    mp4: "video/mp4",
    webm: "video/webm",
    mkv: "video/x-matroska",
    mov: "video/quicktime",
    avi: "video/x-msvideo",
    m4v: "video/mp4",
    ogv: "video/ogg",
    pdf: "application/pdf",
    ppt: "application/vnd.ms-powerpoint",
    pptx: "application/vnd.openxmlformats-officedocument.presentationml.presentation",
    html: "text/html",
    htm: "text/html",
    css: "text/css",
    js: "text/javascript",
    png: "image/png",
    jpg: "image/jpeg",
    jpeg: "image/jpeg",
    gif: "image/gif",
    webp: "image/webp"
  };
  return map[ext] || "application/octet-stream";
}

function isZipFile(file) {
  return /\.zip$/i.test(file.name) || file.type === "application/zip" || file.type === "application/x-zip-compressed";
}

function wait(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

function isNotReadableError(err) {
  const msg = err && err.message ? err.message : String(err || "");
  return err && err.name === "NotReadableError" || /could not be read/i.test(msg) || /permission problems/i.test(msg);
}

async function loadZipWithRetry(file, attempts = 4, delayMs = 400) {
  let lastErr;
  for (let i = 0; i < attempts; i++) {
    try {
      if (i > 0) {
        const probe = file.slice(0, 1);
        await probe.arrayBuffer();
      }
      return await JSZip.loadAsync(file);
    } catch (err) {
      lastErr = err;
      if (!isNotReadableError(err) || i === attempts - 1) throw err;
      await wait(delayMs * (i + 1));
    }
  }
  throw lastErr;
}

function describeZipReadError(file, err) {
  if (isNotReadableError(err)) {
    return `Could not read "${file.name}". The file couldn't be accessed on disk right now — this usually means it's still syncing (OneDrive/Dropbox/Google Drive "online-only" files), still being scanned by antivirus, open in another program, or was moved/renamed after you picked it. Try again in a moment, or copy the file to a local folder (like your Desktop) first and re-select it.`;
  }
  return `Could not read "${file.name}" as a zip archive: ${err && err.message ? err.message : err}`;
}

function isHiddenOrSystemEntryPath(relPath) {
  if (/(^|\/)__MACOSX(\/|$)/.test(relPath)) return true;
  return relPath.split("/").some(part => part.startsWith(".") || /^(thumbs\.db|desktop\.ini)$/i.test(part));
}

function filterUploadedMediaFiles(fileList, mediaType) {
  const allowedExt = ZIP_EXTENSIONS_BY_TYPE[mediaType] || null;
  const result = [];
  let skippedZip = 0;
  for (const file of fileList) {
    const relPath = file.webkitRelativePath || file.name;
    if (isHiddenOrSystemEntryPath(relPath)) continue;
    if (isZipFile(file)) {
      skippedZip++;
      continue;
    }
    const ext = (file.name.split(".").pop() || "").toLowerCase();
    if (allowedExt && !allowedExt.includes(ext)) continue;
    result.push(file);
  }
  if (skippedZip) {
    alert(`Zip files aren't supported here anymore — ${skippedZip} zip file${skippedZip > 1 ? "s were" : " was"} skipped. Choose the files or folder directly instead.`);
  }
  return result;
}

function attachRowClickToggle(li, cb, playBtn) {
  li.addEventListener("click", e => {
    if (e.target === cb || e.target === playBtn) return;
    cb.checked = !cb.checked;
    cb.dispatchEvent(new Event("change"));
  });
}

function updateRangeFill(el) {
  const min = Number(el.min) || 0;
  const max = Number(el.max) || 100;
  const val = Number(el.value);
  const pct = max === min ? 0 : (val - min) / (max - min) * 100;
  el.style.setProperty("--range-fill", `${pct}%`);
}

function getPlaylistMeta(metaObj, name) {
  if (!metaObj[name]) {
    metaObj[name] = {
      pinned: false,
      description: "",
      shuffle: false,
      createdAt: Date.now(),
      modifiedAt: Date.now()
    };
  }
  return metaObj[name];
}

function touchPlaylistMeta(metaObj, name) {
  getPlaylistMeta(metaObj, name).modifiedAt = Date.now();
}

function comparePlaylistNames(playlistsObj, metaObj, mode) {
  return (a, b) => {
    const ma = getPlaylistMeta(metaObj, a);
    const mb = getPlaylistMeta(metaObj, b);
    if (ma.pinned !== mb.pinned) return ma.pinned ? -1 : 1;
    if (mode === "count") return (playlistsObj[b] || []).length - (playlistsObj[a] || []).length;
    if (mode === "modified") return (mb.modifiedAt || 0) - (ma.modifiedAt || 0);
    if (mode === "za") return b.localeCompare(a);
    return a.localeCompare(b);
  };
}

const SMART_RECENT_ADDED = "__smart_recent_added";

const SMART_MOST_PLAYED = "__smart_most_played";

const SMART_RECENT_PLAYED = "__smart_recent_played";

const SMART_PLAYLIST_KEYS = [ SMART_RECENT_ADDED, SMART_MOST_PLAYED, SMART_RECENT_PLAYED ];

function isSmartPlaylist(name) {
  return SMART_PLAYLIST_KEYS.includes(name);
}

function smartPlaylistLabel(name) {
  if (name === SMART_RECENT_ADDED) return "⚡ Recently Added";
  if (name === SMART_MOST_PLAYED) return "🔥 Most Played";
  if (name === SMART_RECENT_PLAYED) return "🕐 Recently Played";
  return name;
}

function buildSmartPlaylistIds(name, mediaArray, historyType) {
  if (name === SMART_RECENT_ADDED) {
    return mediaArray.slice().sort((a, b) => b.id - a.id).slice(0, 25).map(m => m.id);
  }
  if (name === SMART_MOST_PLAYED) {
    return mediaArray.map(m => ({
      id: m.id,
      count: getPlayCount(historyType, m.name)
    })).filter(x => x.count > 0).sort((a, b) => b.count - a.count).slice(0, 25).map(x => x.id);
  }
  if (name === SMART_RECENT_PLAYED) {
    return mediaArray.map(m => ({
      id: m.id,
      last: (historyCache.get(`${historyType}|${m.name}`) || {}).last || ""
    })).filter(x => x.last).sort((a, b) => a.last < b.last ? 1 : a.last > b.last ? -1 : 0).slice(0, 25).map(x => x.id);
  }
  return [];
}

function getActivePlaylistIds(ctx) {
  const name = ctx.getCurrent();
  if (!name) return [];
  if (isSmartPlaylist(name)) return buildSmartPlaylistIds(name, ctx.mediaArray(), ctx.historyType);
  return ctx.playlistsObj[name] || [];
}

function pickNextInList(list, currentId, shuffle) {
  if (!list.length) return null;
  if (shuffle) {
    if (list.length === 1) return list[0] === currentId ? null : list[0];
    let pick;
    let guard = 0;
    do {
      pick = list[Math.floor(Math.random() * list.length)];
      guard++;
    } while (pick === currentId && guard < 20);
    return pick;
  }
  const idx = list.indexOf(currentId);
  const nextIdx = idx + 1;
  return nextIdx < list.length ? list[nextIdx] : null;
}

function reorderIdInList(list, draggedId, targetId) {
  const from = list.indexOf(draggedId);
  const to = list.indexOf(targetId);
  if (from === -1 || to === -1 || from === to) return list;
  list.splice(from, 1);
  list.splice(to, 0, draggedId);
  return list;
}

function renamePlaylistGeneric(ctx) {
  const oldName = ctx.getCurrent();
  if (!oldName || isSmartPlaylist(oldName)) return alert("Select a playlist first");
  const input = prompt("Rename playlist to:", oldName);
  if (input === null) return;
  const trimmed = input.trim();
  if (!trimmed) return alert("Playlist name cannot be empty.");
  if (trimmed === oldName) return;
  if (ctx.playlistsObj[trimmed]) return alert(`A playlist named "${trimmed}" already exists.`);
  ctx.playlistsObj[trimmed] = ctx.playlistsObj[oldName];
  delete ctx.playlistsObj[oldName];
  if (ctx.metaObj[oldName]) {
    ctx.metaObj[trimmed] = ctx.metaObj[oldName];
    delete ctx.metaObj[oldName];
  }
  touchPlaylistMeta(ctx.metaObj, trimmed);
  ctx.setCurrent(trimmed);
  if (ctx.titleEl) ctx.titleEl.textContent = trimmed;
  ctx.saveFn();
  ctx.saveMetaFn();
  ctx.renderNamesFn();
  if (ctx.renderTracksFn) ctx.renderTracksFn();
}

function duplicatePlaylistGeneric(ctx, name) {
  if (isSmartPlaylist(name)) return alert("Smart playlists cannot be duplicated.");
  const base = `${name} Copy`;
  let finalName = base;
  let n = 2;
  while (ctx.playlistsObj[finalName]) finalName = `${base} ${n++}`;
  ctx.playlistsObj[finalName] = [ ...ctx.playlistsObj[name] || [] ];
  const srcMeta = getPlaylistMeta(ctx.metaObj, name);
  ctx.metaObj[finalName] = {
    pinned: false,
    description: srcMeta.description,
    shuffle: srcMeta.shuffle,
    createdAt: Date.now(),
    modifiedAt: Date.now()
  };
  ctx.saveFn();
  ctx.saveMetaFn();
  ctx.renderNamesFn();
}

function mergePlaylistGeneric(ctx) {
  const targetName = ctx.getCurrent();
  if (!targetName || isSmartPlaylist(targetName)) return alert("Select a playlist first");
  const others = Object.keys(ctx.playlistsObj).filter(n => n !== targetName);
  if (!others.length) return alert("No other playlists to merge from.");
  const sourceName = prompt(`Merge which playlist into "${targetName}"?\nAvailable: ${others.join(", ")}`);
  if (!sourceName) return;
  if (!ctx.playlistsObj[sourceName]) return alert(`Playlist "${sourceName}" not found.`);
  const merged = ctx.playlistsObj[targetName].slice();
  ctx.playlistsObj[sourceName].forEach(id => {
    if (!merged.includes(id)) merged.push(id);
  });
  ctx.playlistsObj[targetName] = merged;
  touchPlaylistMeta(ctx.metaObj, targetName);
  ctx.saveFn();
  ctx.saveMetaFn();
  ctx.renderNamesFn();
  if (ctx.renderTracksFn) ctx.renderTracksFn();
}

function togglePinPlaylist(ctx, name) {
  if (isSmartPlaylist(name)) return;
  const meta = getPlaylistMeta(ctx.metaObj, name);
  meta.pinned = !meta.pinned;
  ctx.saveMetaFn();
  ctx.renderNamesFn();
}

function toggleShufflePlaylist(ctx) {
  const name = ctx.getCurrent();
  if (!name || isSmartPlaylist(name)) return;
  const meta = getPlaylistMeta(ctx.metaObj, name);
  meta.shuffle = !meta.shuffle;
  ctx.saveMetaFn();
  return meta.shuffle;
}

function moveOrCopyTrack(ctx, id, targetName, isMove) {
  if (!ctx.playlistsObj[targetName]) return;
  if (!ctx.playlistsObj[targetName].includes(id)) ctx.playlistsObj[targetName].push(id);
  touchPlaylistMeta(ctx.metaObj, targetName);
  if (isMove) {
    const current = ctx.getCurrent();
    ctx.playlistsObj[current] = ctx.playlistsObj[current].filter(x => x !== id);
    touchPlaylistMeta(ctx.metaObj, current);
  }
  ctx.saveFn();
  ctx.saveMetaFn();
}

function buildCustomSortDropdown(options, initialValue, onChange) {
  const wrapper = document.createElement("div");
  wrapper.className = "custom-dropdown playlist-sort-dropdown";
  const toggle = document.createElement("button");
  toggle.type = "button";
  toggle.className = "custom-dropdown-toggle";
  toggle.setAttribute("aria-haspopup", "listbox");
  toggle.setAttribute("aria-expanded", "false");
  const valueSpan = document.createElement("span");
  valueSpan.className = "custom-dropdown-value";
  const arrowSpan = document.createElement("span");
  arrowSpan.className = "custom-dropdown-arrow";
  arrowSpan.setAttribute("aria-hidden", "true");
  arrowSpan.textContent = "▾";
  toggle.append(valueSpan, arrowSpan);
  const menu = document.createElement("ul");
  menu.className = "custom-dropdown-menu";
  menu.setAttribute("role", "listbox");
  menu.tabIndex = -1;
  menu.hidden = true;
  const select = document.createElement("select");
  select.className = "sort-select sort-select--hidden";
  select.tabIndex = -1;
  select.setAttribute("aria-hidden", "true");
  select.title = "Sort your playlists";
  options.forEach(([val, label]) => {
    const li = document.createElement("li");
    li.setAttribute("role", "option");
    li.className = "custom-dropdown-option";
    li.dataset.value = val;
    li.textContent = label;
    if (val === initialValue) {
      li.classList.add("selected");
      li.setAttribute("aria-selected", "true");
      valueSpan.textContent = label;
    } else {
      li.setAttribute("aria-selected", "false");
    }
    menu.appendChild(li);
    const opt = document.createElement("option");
    opt.value = val;
    opt.textContent = label;
    select.appendChild(opt);
  });
  select.value = initialValue;
  select.addEventListener("change", () => onChange(select.value));
  wrapper.append(toggle, menu);
  const frag = document.createDocumentFragment();
  frag.append(wrapper, select);
  initCustomDropdown(wrapper, select);
  return frag;
}

function buildPlaylistToolbar(ctx) {
  const wrap = document.createElement("div");
  wrap.className = "playlist-toolbar";
  const dropdownFrag = buildCustomSortDropdown([ [ "name", "Name (A→Z)" ], [ "za", "Name (Z→A)" ], [ "count", "Track Count" ], [ "modified", "Recently Modified" ] ], ctx.getSortMode(), val => {
    ctx.setSortMode(val);
    ctx.renderNamesFn();
  });
  const mergeBtn = document.createElement("button");
  mergeBtn.className = "action-button playlist-toolbar-btn playlist-toolbar-btn--merge";
  mergeBtn.textContent = "🔗 Merge Into Selected";
  mergeBtn.title = "Merge another playlist into the selected one";
  mergeBtn.addEventListener("click", () => mergePlaylistGeneric(ctx));
  wrap.append(dropdownFrag, mergeBtn);
  return wrap;
}

function buildPlaylistListItem(ctx, name) {
  const li = document.createElement("li");
  li.dataset.playlistName = name;
  const smart = isSmartPlaylist(name);
  if (name === ctx.getCurrent()) li.classList.add("selected");
  if (smart) li.classList.add("smart-playlist-item");
  const nameEl = document.createElement("span");
  nameEl.className = "playlist-item-name";
  const count = smart ? buildSmartPlaylistIds(name, ctx.mediaArray(), ctx.historyType).length : (ctx.playlistsObj[name] || []).length;
  nameEl.textContent = smart ? smartPlaylistLabel(name) : name;
  li.appendChild(nameEl);
  const countEl = document.createElement("span");
  countEl.className = "playlist-item-count";
  countEl.textContent = count;
  li.appendChild(countEl);
  if (!smart) {
    const meta = getPlaylistMeta(ctx.metaObj, name);
    const pinBtn = document.createElement("button");
    pinBtn.className = "playlist-item-icon-btn";
    pinBtn.textContent = meta.pinned ? "📌" : "📍";
    pinBtn.title = meta.pinned ? "Unpin playlist" : "Pin playlist";
    pinBtn.addEventListener("click", e => {
      e.stopPropagation();
      togglePinPlaylist(ctx, name);
    });
    const renameBtn = document.createElement("button");
    renameBtn.className = "playlist-item-icon-btn";
    renameBtn.textContent = "✏️";
    renameBtn.title = "Rename playlist";
    renameBtn.addEventListener("click", e => {
      e.stopPropagation();
      if (ctx.getCurrent() !== name) {
        ctx.setCurrent(name);
        if (ctx.titleEl) ctx.titleEl.textContent = name;
      }
      renamePlaylistGeneric(ctx);
    });
    const dupBtn = document.createElement("button");
    dupBtn.className = "playlist-item-icon-btn";
    dupBtn.textContent = "⧉";
    dupBtn.title = "Duplicate playlist";
    dupBtn.addEventListener("click", e => {
      e.stopPropagation();
      duplicatePlaylistGeneric(ctx, name);
    });
    const actionsEl = document.createElement("div");
    actionsEl.className = "playlist-item-actions";
    actionsEl.append(pinBtn, renameBtn, dupBtn);
    li.appendChild(actionsEl);
    li.addEventListener("dragover", e => {
      if (!e.dataTransfer.types.includes("text/plain")) return;
      e.preventDefault();
      e.dataTransfer.dropEffect = "copy";
      li.classList.add("drag-over");
    });
    li.addEventListener("dragleave", () => li.classList.remove("drag-over"));
    li.addEventListener("drop", e => {
      e.preventDefault();
      li.classList.remove("drag-over");
      const id = Number(e.dataTransfer.getData("text/plain"));
      if (!id || !ctx.mediaArray().find(m => m.id === id)) return;
      if (!ctx.playlistsObj[name].includes(id)) ctx.playlistsObj[name].push(id);
      touchPlaylistMeta(ctx.metaObj, name);
      ctx.saveFn();
      ctx.saveMetaFn();
      ctx.renderNamesFn();
      if (ctx.getCurrent() === name && ctx.renderTracksFn) ctx.renderTracksFn();
    });
  }
  li.addEventListener("click", () => ctx.selectFn(name));
  return li;
}

function renderPlaylistNamesGeneric(ctx) {
  if (ctx.toolbarEl && !ctx.toolbarEl.dataset.built) {
    ctx.toolbarEl.innerHTML = "";
    ctx.toolbarEl.appendChild(buildPlaylistToolbar(ctx));
    ctx.toolbarEl.dataset.built = "1";
  }
  ctx.listEl.innerHTML = "";
  SMART_PLAYLIST_KEYS.forEach(key => {
    ctx.listEl.appendChild(buildPlaylistListItem(ctx, key));
  });
  Object.keys(ctx.playlistsObj).sort(comparePlaylistNames(ctx.playlistsObj, ctx.metaObj, ctx.getSortMode())).forEach(name => ctx.listEl.appendChild(buildPlaylistListItem(ctx, name)));
}

function getTrackSortMode(ctx) {
  return appGet(`trackSortMode:${ctx.historyType}`, null);
}

function setTrackSortMode(ctx, mode) {
  appSet(`trackSortMode:${ctx.historyType}`, mode);
}

function applyTrackSortMode(ctx, ids) {
  const mode = getTrackSortMode(ctx);
  if (!mode) return ids;
  const media = ctx.mediaArray();
  const sorted = ids.slice();
  sorted.sort((a, b) => {
    const ma = media.find(m => m.id === a);
    const mb = media.find(m => m.id === b);
    const na = ma ? ma.name : "";
    const nb = mb ? mb.name : "";
    return mode === "za" ? nb.localeCompare(na) : na.localeCompare(nb);
  });
  return sorted;
}

function buildPlaylistDetailHeader(ctx) {
  const name = ctx.getCurrent();
  const wrap = document.createElement("div");
  wrap.className = "playlist-detail-header";
  const smart = name ? isSmartPlaylist(name) : false;
  const sortAzTrackBtn = document.createElement("button");
  sortAzTrackBtn.className = "action-button playlist-toolbar-btn";
  sortAzTrackBtn.textContent = "Sort A→Z";
  sortAzTrackBtn.addEventListener("click", () => {
    if (!ctx.getCurrent()) return alert("Select a playlist first");
    setTrackSortMode(ctx, "az");
    ctx.renderTracksFn();
  });
  const sortZaTrackBtn = document.createElement("button");
  sortZaTrackBtn.className = "action-button playlist-toolbar-btn";
  sortZaTrackBtn.textContent = "Sort Z→A";
  sortZaTrackBtn.addEventListener("click", () => {
    if (!ctx.getCurrent()) return alert("Select a playlist first");
    setTrackSortMode(ctx, "za");
    ctx.renderTracksFn();
  });
  const sortGroup = document.createElement("div");
  sortGroup.className = "playlist-sort-group";
  sortGroup.append(sortAzTrackBtn, sortZaTrackBtn);
  if (!name) {
    const shuffleBtn = document.createElement("button");
    shuffleBtn.className = "action-button playlist-toolbar-btn playlist-shuffle-btn";
    shuffleBtn.innerHTML = '<span class="playlist-shuffle-icon">🔀</span> Shuffle: Off';
    shuffleBtn.addEventListener("click", () => alert("Select a playlist first"));
    wrap.append(sortGroup, shuffleBtn);
    return wrap;
  }
  if (!smart) {
    const meta = getPlaylistMeta(ctx.metaObj, name);
    const shuffleBtn = document.createElement("button");
    const setShuffleBtnState = on => {
      shuffleBtn.className = `action-button playlist-toolbar-btn playlist-shuffle-btn${on ? " is-on" : ""}`;
      shuffleBtn.innerHTML = `<span class="playlist-shuffle-icon">🔀</span> Shuffle: ${on ? "On" : "Off"}`;
    };
    setShuffleBtnState(meta.shuffle);
    shuffleBtn.addEventListener("click", () => {
      const on = toggleShufflePlaylist(ctx);
      setShuffleBtnState(on);
    });
    const descInput = document.createElement("input");
    descInput.type = "text";
    descInput.className = "playlist-input playlist-description-input";
    descInput.placeholder = "Add a description...";
    descInput.value = meta.description || "";
    descInput.addEventListener("change", () => {
      meta.description = descInput.value.trim();
      touchPlaylistMeta(ctx.metaObj, name);
      ctx.saveMetaFn();
    });
    wrap.append(sortGroup, shuffleBtn, descInput);
  } else {
    const note = document.createElement("span");
    note.className = "smart-playlist-note";
    note.textContent = "Smart playlist — auto-generated, updates automatically.";
    wrap.append(sortGroup, note);
  }
  return wrap;
}

function buildTrackRow(ctx, id) {
  const media = ctx.mediaArray().find(m => m.id === id);
  if (!media) return null;
  const name = ctx.getCurrent();
  const smart = isSmartPlaylist(name);
  const li = document.createElement("li");
  li.dataset.id = id;
  if (id === ctx.currentPlayingId()) li.classList.add("selected");
  if (!smart) {
    li.draggable = true;
    li.addEventListener("dragstart", e => {
      e.dataTransfer.setData("application/x-track-reorder", String(id));
      li.classList.add("dragging-track");
    });
    li.addEventListener("dragend", () => li.classList.remove("dragging-track"));
    li.addEventListener("dragover", e => {
      if (!e.dataTransfer.types.includes("application/x-track-reorder")) return;
      e.preventDefault();
      li.classList.add("drag-over");
    });
    li.addEventListener("dragleave", () => li.classList.remove("drag-over"));
    li.addEventListener("drop", e => {
      e.preventDefault();
      li.classList.remove("drag-over");
      const draggedId = Number(e.dataTransfer.getData("application/x-track-reorder"));
      if (!draggedId || draggedId === id) return;
      reorderIdInList(ctx.playlistsObj[name], draggedId, id);
      touchPlaylistMeta(ctx.metaObj, name);
      ctx.saveFn();
      ctx.renderTracksFn();
    });
  }
  const cb = document.createElement("input");
  cb.type = "checkbox";
  cb.dataset.id = id;
  cb.disabled = smart;
  cb.addEventListener("change", () => li.classList.toggle("selected", cb.checked));
  const nameEl = document.createElement("span");
  nameEl.textContent = media.name;
  const playBtn = document.createElement("button");
  playBtn.textContent = "▶";
  playBtn.className = "media-row-play-btn";
  playBtn.addEventListener("click", () => {
    ctx.setPlaying(true);
    ctx.playByIdFn(id);
  });
  li.append(cb, nameEl, playBtn);
  if (!smart) {
    const moveBtn = document.createElement("button");
    moveBtn.textContent = "⇒";
    moveBtn.title = "Copy or move to another playlist";
    moveBtn.addEventListener("click", () => {
      const others = Object.keys(ctx.playlistsObj).filter(n => n !== name);
      if (!others.length) return alert("No other playlists available.");
      const target = prompt(`Copy to which playlist? (type "move:Name" to move instead)\nAvailable: ${others.join(", ")}`);
      if (!target) return;
      let isMove = false;
      let targetName = target.trim();
      if (targetName.toLowerCase().startsWith("move:")) {
        isMove = true;
        targetName = targetName.slice(5).trim();
      }
      if (!ctx.playlistsObj[targetName]) return alert(`Playlist "${targetName}" not found.`);
      moveOrCopyTrack(ctx, id, targetName, isMove);
      ctx.renderNamesFn();
      ctx.renderTracksFn();
    });
    li.appendChild(moveBtn);
  }
  attachRowClickToggle(li, cb, playBtn);
  return li;
}

function renderPlaylistTracksGeneric(ctx) {
  const name = ctx.getCurrent();
  ctx.tracksEl.innerHTML = "";
  if (ctx.headerEl) {
    ctx.headerEl.innerHTML = "";
    ctx.headerEl.appendChild(buildPlaylistDetailHeader(ctx));
  }
  if (!name) return;
  const ids = applyTrackSortMode(ctx, getActivePlaylistIds(ctx));
  ids.forEach(id => {
    const row = buildTrackRow(ctx, id);
    if (row) ctx.tracksEl.appendChild(row);
  });
}

let appDB = null;

let appDataCache = new Map;

let currentUserId = null;

const GUEST_USER_ID = "guest";

function userKey(key) {
  return currentUserId ? `u${currentUserId}:${key}` : key;
}

function openIndexedDBSafely(name, version, onUpgradeNeeded, timeoutMs = 8e3) {
  return new Promise((resolve, reject) => {
    let settled = false;
    const timer = setTimeout(() => {
      if (settled) return;
      settled = true;
      reject(new Error(`Timed out opening IndexedDB database "${name}". It may be blocked by another tab or by browser storage settings.`));
    }, timeoutMs);
    let req;
    try {
      req = indexedDB.open(name, version);
    } catch (err) {
      clearTimeout(timer);
      settled = true;
      reject(err);
      return;
    }
    req.onupgradeneeded = e => {
      if (onUpgradeNeeded) onUpgradeNeeded(e);
    };
    req.onsuccess = e => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      resolve(e.target.result);
    };
    req.onerror = () => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      reject(req.error || new Error(`Failed to open IndexedDB database "${name}".`));
    };
    req.onblocked = () => {
      if (settled) return;
      settled = true;
      clearTimeout(timer);
      reject(new Error(`IndexedDB database "${name}" is blocked, likely by another open tab of this app.`));
    };
  });
}

function openAppDB() {
  return openIndexedDBSafely("AppStateDB", 1, e => {
    const db = e.target.result;
    if (!db.objectStoreNames.contains("kv")) db.createObjectStore("kv");
  });
}

function loadAllAppData(db) {
  return new Promise(resolve => {
    appDataCache.clear();
    const tx = db.transaction("kv", "readonly");
    const store = tx.objectStore("kv");
    const req = store.openCursor();
    req.onsuccess = e => {
      const cursor = e.target.result;
      if (cursor) {
        appDataCache.set(cursor.key, cursor.value);
        cursor.continue();
      } else {
        resolve();
      }
    };
    req.onerror = () => resolve();
  });
}

function appGet(key, fallback) {
  const k = userKey(key);
  return appDataCache.has(k) ? appDataCache.get(k) : fallback;
}

function appSet(key, value) {
  const k = userKey(key);
  appDataCache.set(k, value);
  if (!appDB) return;
  const tx = appDB.transaction("kv", "readwrite");
  tx.objectStore("kv").put(value, k);
  tx.onerror = () => console.error("Failed to persist app data for key", k, tx.error);
}

function appDeleteAllForUser(userId) {
  if (!appDB) return Promise.resolve();
  const prefix = `u${userId}:`;
  const keysToDelete = [ ...appDataCache.keys() ].filter(k => k.startsWith(prefix));
  keysToDelete.forEach(k => appDataCache.delete(k));
  return new Promise(resolve => {
    const tx = appDB.transaction("kv", "readwrite");
    const store = tx.objectStore("kv");
    keysToDelete.forEach(k => store.delete(k));
    tx.oncomplete = () => resolve();
    tx.onerror = () => resolve();
  });
}

function isValidPasskeyValue(value) {
  const trimmed = String(value || "").trim();
  if (!/^\d+$/.test(trimmed)) return false;
  const max = novaConfig && novaConfig.recoveryPasskey && novaConfig.recoveryPasskey.max || 1e12;
  const num = Number(trimmed);
  if (!Number.isFinite(num)) return false;
  if (num < 0 || num > max) return false;
  return true;
}

function normalizePasskeyValue(value) {
  const trimmed = String(value || "").trim();
  const stripped = trimmed.replace(/^0+(?=\d)/, "");
  return stripped === "" ? "0" : stripped;
}

const RESET_MAX_ATTEMPTS = 5;

const RESET_LOCKOUT_MS = 6e4;

function resetLockoutStorageKey(identifier) {
  return `resetLockout:${identifier.trim().toLowerCase()}`;
}

function getResetLockoutState(identifier) {
  if (!identifier) return null;
  try {
    const raw = localStorage.getItem(resetLockoutStorageKey(identifier));
    if (!raw) return null;
    const parsed = JSON.parse(raw);
    if (!parsed || typeof parsed.attempts !== "number") return null;
    return parsed;
  } catch {
    return null;
  }
}

function setResetLockoutState(identifier, state) {
  if (!identifier) return;
  try {
    localStorage.setItem(resetLockoutStorageKey(identifier), JSON.stringify(state));
  } catch {
    console.error("Could not persist reset lockout state.");
  }
}

function clearResetLockoutState(identifier) {
  if (!identifier) return;
  try {
    localStorage.removeItem(resetLockoutStorageKey(identifier));
  } catch {
    console.error("Could not clear reset lockout state.");
  }
}

function recordFailedResetAttempt(identifier) {
  if (!identifier) return null;
  const existing = getResetLockoutState(identifier) || {
    attempts: 0,
    lockedUntil: null
  };
  existing.attempts += 1;
  if (existing.attempts >= RESET_MAX_ATTEMPTS) {
    existing.lockedUntil = Date.now() + RESET_LOCKOUT_MS;
  }
  setResetLockoutState(identifier, existing);
  return existing;
}

function isResetLockedOut(identifier) {
  const state = getResetLockoutState(identifier);
  if (!state || !state.lockedUntil) return false;
  return state.lockedUntil > Date.now();
}

const LOGIN_MAX_ATTEMPTS = 5;

const LOGIN_LOCKOUT_MS = 4e4;

const LOGIN_PASSWORD_PROMPT_AT = LOGIN_MAX_ATTEMPTS - 1;

const LOCKOUT_ACTIVE_IDENTIFIER_KEY = "loginLockout:activeIdentifier";

let lockoutTickInterval = null;

function lockoutStorageKey(identifier) {
  return `loginLockout:${identifier.trim().toLowerCase()}`;
}

function setActiveLockoutIdentifier(identifier) {
  try {
    localStorage.setItem(LOCKOUT_ACTIVE_IDENTIFIER_KEY, identifier.trim().toLowerCase());
  } catch {
    console.error("Could not persist active lockout identifier.");
  }
}

function getActiveLockoutIdentifier() {
  try {
    return localStorage.getItem(LOCKOUT_ACTIVE_IDENTIFIER_KEY);
  } catch {
    return null;
  }
}

function clearActiveLockoutIdentifier() {
  try {
    localStorage.removeItem(LOCKOUT_ACTIVE_IDENTIFIER_KEY);
  } catch {
    console.error("Could not clear active lockout identifier.");
  }
}

function getLockoutState(identifier) {
  if (!identifier) return null;
  try {
    const raw = localStorage.getItem(lockoutStorageKey(identifier));
    if (!raw) return null;
    const parsed = JSON.parse(raw);
    if (!parsed || typeof parsed.attempts !== "number") return null;
    return parsed;
  } catch {
    return null;
  }
}

function setLockoutState(identifier, state) {
  if (!identifier) return;
  try {
    localStorage.setItem(lockoutStorageKey(identifier), JSON.stringify(state));
  } catch {
    console.error("Could not persist lockout state to localStorage.");
  }
}

function clearLockoutState(identifier) {
  if (!identifier) return;
  try {
    localStorage.removeItem(lockoutStorageKey(identifier));
  } catch {
    console.error("Could not clear lockout state from localStorage.");
  }
}

function recordFailedAttempt(identifier) {
  if (!identifier) return null;
  const existing = getLockoutState(identifier) || {
    attempts: 0,
    lockedUntil: null
  };
  existing.attempts += 1;
  if (existing.attempts >= LOGIN_MAX_ATTEMPTS) {
    existing.lockedUntil = Date.now() + LOGIN_LOCKOUT_MS;
  }
  setLockoutState(identifier, existing);
  setActiveLockoutIdentifier(identifier);
  return existing;
}

function isCurrentlyLockedOut(identifier) {
  const state = getLockoutState(identifier);
  if (!state || !state.lockedUntil) return false;
  return state.lockedUntil > Date.now();
}

function stopLockoutCountdown() {
  if (lockoutTickInterval) {
    clearInterval(lockoutTickInterval);
    lockoutTickInterval = null;
  }
}

function startLockoutCountdown(identifier, statusEl, loginBtn, identifierInput, passwordInput) {
  stopLockoutCountdown();
  const tick = () => {
    const state = getLockoutState(identifier);
    if (!state || !state.lockedUntil || state.lockedUntil <= Date.now()) {
      stopLockoutCountdown();
      clearLockoutState(identifier);
      clearActiveLockoutIdentifier();
      loginBtn.disabled = false;
      identifierInput.disabled = false;
      passwordInput.disabled = false;
      statusEl.textContent = "";
      statusEl.classList.remove("status-lockout");
      hideForgotPasswordPrompt();
      return;
    }
    const secondsLeft = Math.ceil((state.lockedUntil - Date.now()) / 1e3);
    statusEl.textContent = `Too many failed attempts (${state.attempts}/${LOGIN_MAX_ATTEMPTS}). Account locked. Please try again in ${secondsLeft} second${secondsLeft === 1 ? "" : "s"}...`;
    statusEl.classList.add("status-lockout");
  };
  loginBtn.disabled = true;
  identifierInput.disabled = true;
  passwordInput.disabled = true;
  tick();
  lockoutTickInterval = setInterval(tick, 1e3);
}

function checkAndApplyLockoutOnLoad(identifier, statusEl, loginBtn, identifierInput, passwordInput) {
  if (!identifier) return false;
  if (isCurrentlyLockedOut(identifier)) {
    startLockoutCountdown(identifier, statusEl, loginBtn, identifierInput, passwordInput);
    return true;
  }
  return false;
}

function reapplyLockoutOnPageLoad(statusEl, loginBtn, identifierInput, passwordInput) {
  const identifier = getActiveLockoutIdentifier();
  if (!identifier) return;
  const state = getLockoutState(identifier);
  if (!state) return;
  if (state.lockedUntil && state.lockedUntil > Date.now()) {
    identifierInput.value = identifier;
    startLockoutCountdown(identifier, statusEl, loginBtn, identifierInput, passwordInput);
  } else if (state.attempts >= LOGIN_PASSWORD_PROMPT_AT && !state.lockedUntil) {
    identifierInput.value = identifier;
    showForgotPasswordPrompt(identifier);
  }
}

function showForgotPasswordPrompt(identifier) {
  const link = document.getElementById("forgot-password-link");
  if (!link) return;
  link.style.display = "block";
  link.dataset.identifier = identifier;
}

function hideForgotPasswordPrompt() {
  const link = document.getElementById("forgot-password-link");
  if (!link) return;
  link.style.display = "none";
  delete link.dataset.identifier;
}

function dismissFirstTimeBanner() {
  const banner = document.getElementById("no-account-banner");
  if (banner) banner.classList.add("dismissed");
}

class UserAccountSystem {
  constructor() {
    this.db = null;
    this.currentUser = null;
    this.sessionToken = null;
    this.autoLogin = localStorage.getItem("autoLogin") === "true";
    this.userId = null;
    this.isGuest = false;
    this.elements = {
      signinForm: document.getElementById("signin-form"),
      signupForm: document.getElementById("signup-form"),
      guestForm: document.getElementById("guest-form"),
      loginBtn: document.getElementById("login-btn"),
      signupBtn: document.getElementById("signup-btn"),
      continueGuestBtn: document.getElementById("continue-guest-btn"),
      logoutBtn: document.getElementById("logout-btn"),
      accountUsername: document.getElementById("account-username"),
      accountEmail: document.getElementById("account-email"),
      accountCreated: document.getElementById("account-created"),
      accountMediaCount: document.getElementById("account-media-count"),
      accountStorage: document.getElementById("account-storage"),
      changeUsernameBtn: document.getElementById("change-username-btn"),
      changePasswordBtn: document.getElementById("change-password-btn"),
      changeEmailBtn: document.getElementById("change-email-btn"),
      listUsersBtn: document.getElementById("list-users-btn"),
      deleteAccountBtn: document.getElementById("delete-account-btn"),
      exportDataBtn: document.getElementById("export-user-data"),
      importDataBtn: document.getElementById("import-user-data"),
      autoLoginCheckbox: document.getElementById("auto-login"),
      rememberPlaybackCheckbox: document.getElementById("remember-playback"),
      keepHistoryCheckbox: document.getElementById("keep-history"),
      status: document.getElementById("login-status"),
      refreshUsersBtn: document.getElementById("refresh-users-btn"),
      loginIdentifierInput: document.getElementById("login-username"),
      loginPasswordInput: document.getElementById("login-password")
    };
    this.lastActiveTerminal = "music";
    this.init();
  }
  async init() {
    this.showLoginPage();
    this.setupTabs();
    this.setupEventListeners();
    this.elements.status.textContent = "Loading account system...";
    try {
      this.db = await this.openAccountsDB();
      this.elements.status.textContent = "";
      const existingUsers = await this.getAllUsers();
      if (existingUsers.length > 0) dismissFirstTimeBanner();
      const savedSession = localStorage.getItem("sessionToken");
      const autoLoginEnabled = localStorage.getItem("autoLogin") === "true";
      if (savedSession && autoLoginEnabled) {
        const session = await this.validateSession(savedSession);
        if (session) {
          await this.activateUser(session.user, savedSession);
          this.showTerminalHubPage();
          return;
        }
      }
      reapplyLockoutOnPageLoad(this.elements.status, this.elements.loginBtn, this.elements.loginIdentifierInput, this.elements.loginPasswordInput);
    } catch (err) {
      console.error("Failed to initialize account system:", err);
      this.elements.status.textContent = "Could not access local account storage. Check your browser's site data / storage settings, then refresh.";
    }
  }
  openAccountsDB() {
    return openIndexedDBSafely("UserAccountsDB", 1, e => {
      const db = e.target.result;
      if (!db.objectStoreNames.contains("users")) {
        const userStore = db.createObjectStore("users", {
          keyPath: "id",
          autoIncrement: true
        });
        userStore.createIndex("username", "username", {
          unique: true
        });
        userStore.createIndex("email", "email", {
          unique: false
        });
        userStore.createIndex("createdAt", "createdAt");
      }
      if (!db.objectStoreNames.contains("sessions")) {
        const sessionStore = db.createObjectStore("sessions", {
          keyPath: "token"
        });
        sessionStore.createIndex("userId", "userId");
        sessionStore.createIndex("expiresAt", "expiresAt");
      }
      if (!db.objectStoreNames.contains("settings")) {
        db.createObjectStore("settings", {
          keyPath: "userId"
        });
      }
    });
  }
  clearLoginFormState() {
    const activeIdentifier = getActiveLockoutIdentifier();
    const stillLocked = activeIdentifier && isCurrentlyLockedOut(activeIdentifier);
    this.elements.status.classList.remove("status-success");
    document.getElementById("signup-username").value = "";
    document.getElementById("signup-email").value = "";
    document.getElementById("signup-password").value = "";
    document.getElementById("signup-confirm").value = "";
    document.getElementById("reset-email").value = "";
    document.getElementById("reset-new-password").value = "";
    document.getElementById("reset-confirm-password").value = "";
    if (stillLocked) {
      this.elements.loginIdentifierInput.value = activeIdentifier;
      startLockoutCountdown(activeIdentifier, this.elements.status, this.elements.loginBtn, this.elements.loginIdentifierInput, this.elements.loginPasswordInput);
      return;
    }
    this.elements.status.textContent = "";
    this.elements.status.classList.remove("status-lockout");
    document.getElementById("login-username").value = "";
    document.getElementById("login-password").value = "";
    stopLockoutCountdown();
    hideForgotPasswordPrompt();
    this.elements.loginBtn.disabled = false;
    this.elements.loginIdentifierInput.disabled = false;
    this.elements.loginPasswordInput.disabled = false;
    if (activeIdentifier) {
      const state = getLockoutState(activeIdentifier);
      if (state && state.attempts >= LOGIN_PASSWORD_PROMPT_AT && !state.lockedUntil) {
        showForgotPasswordPrompt(activeIdentifier);
      }
    }
  }
  setupTabs() {
    const tabs = document.querySelectorAll(".tab-btn");
    tabs.forEach(tab => {
      tab.addEventListener("click", () => {
        tabs.forEach(t => t.classList.remove("active"));
        tab.classList.add("active");
        const formId = `${tab.dataset.tab}-form`;
        document.querySelectorAll(".login-form").forEach(f => f.classList.remove("active"));
        document.getElementById(formId).classList.add("active");
        this.clearLoginFormState();
      });
    });
  }
  setupEventListeners() {
    this.elements.loginBtn.addEventListener("click", async () => {
      const identifier = this.elements.loginIdentifierInput.value.trim();
      const password = this.elements.loginPasswordInput.value;
      if (checkAndApplyLockoutOnLoad(identifier, this.elements.status, this.elements.loginBtn, this.elements.loginIdentifierInput, this.elements.loginPasswordInput)) {
        return;
      }
      if (!identifier && !password) {
        this.elements.status.textContent = "All fields are required. Please enter your credentials.";
        this.elements.status.classList.remove("status-lockout", "status-success");
        return;
      }
      if (!identifier && password) {
        this.elements.status.textContent = "Please enter your Username or Email.";
        this.elements.status.classList.remove("status-lockout", "status-success");
        return;
      }
      if (identifier && !password) {
        this.elements.status.textContent = "Please enter your Password.";
        this.elements.status.classList.remove("status-lockout", "status-success");
        return;
      }
      const success = await this.signIn(identifier, password);
      if (success) {
        clearLockoutState(identifier);
        dismissFirstTimeBanner();
        this.showTerminalHubPage();
      }
    });
    this.elements.signupBtn.addEventListener("click", async () => {
      const username = document.getElementById("signup-username").value.trim();
      const email = document.getElementById("signup-email").value.trim();
      const password = document.getElementById("signup-password").value;
      const confirm = document.getElementById("signup-confirm").value;
      const passkey = document.getElementById("signup-passkey").value.trim();
      this.elements.status.classList.remove("status-lockout", "status-success");
      if (!username && !email && !password && !confirm && !passkey) {
        this.elements.status.textContent = "All fields are required. Please enter your credentials.";
        return;
      }
      if (!username) {
        this.elements.status.textContent = "Please enter a Username.";
        return;
      }
      if (!email) {
        this.elements.status.textContent = "Please enter your Email.";
        return;
      }
      if (!this.isValidEmail(email)) {
        this.elements.status.textContent = "Please enter a valid email address.";
        return;
      }
      if (!password) {
        this.elements.status.textContent = "Please enter a Password.";
        return;
      }
      if (!confirm) {
        this.elements.status.textContent = "Please confirm your Password.";
        return;
      }
      if (password !== confirm) {
        this.elements.status.textContent = "Passwords do not match.";
        return;
      }
      if (!passkey) {
        this.elements.status.textContent = "Please set a recovery passkey number.";
        return;
      }
      if (!isValidPasskeyValue(passkey)) {
        this.elements.status.textContent = "Recovery passkey must be a whole number between 0 and 1,000,000,000,000.";
        return;
      }
      const success = await this.createAccount(username, email, password, passkey);
      if (success) {
        this.elements.status.classList.add("status-success");
        dismissFirstTimeBanner();
        document.getElementById("signup-username").value = "";
        document.getElementById("signup-email").value = "";
        document.getElementById("signup-password").value = "";
        document.getElementById("signup-confirm").value = "";
        document.getElementById("signup-passkey").value = "";
        document.querySelector('.tab-btn[data-tab="signin"]').click();
      }
    });
    if (this.elements.continueGuestBtn) {
      this.elements.continueGuestBtn.addEventListener("click", () => this.continueAsGuest());
    }
    const guestCreateAccountBtn = document.getElementById("guest-create-account-btn");
    if (guestCreateAccountBtn) {
      guestCreateAccountBtn.addEventListener("click", () => {
        const signupTab = document.querySelector('.tab-btn[data-tab="signup"]');
        if (signupTab) signupTab.click();
      });
    }
    const guestBannerCta = document.getElementById("guest-account-banner-cta");
    if (guestBannerCta) {
      guestBannerCta.addEventListener("click", () => {
        this.signOut();
        const signupTab = document.querySelector('.tab-btn[data-tab="signup"]');
        if (signupTab) signupTab.click();
      });
    }
    this.elements.logoutBtn.addEventListener("click", () => this.signOut());
    [ "logout-btn-music", "logout-btn-video", "logout-btn-documentary", "logout-btn-movie", "logout-btn-comedy", "logout-btn-webseries", "logout-btn-podcast", "logout-btn-games", "logout-btn-books", "logout-btn-bookmarks", "logout-btn-hub", "logout-btn-gamevideo", "logout-btn-gamemovie", "logout-btn-bookvideo", "logout-btn-bookmovie", "logout-btn-presentations" ].forEach(id => {
      const btn = document.getElementById(id);
      if (btn) btn.addEventListener("click", () => this.signOut());
    });
    this.elements.changePasswordBtn.addEventListener("click", () => this.changePassword());
    this.elements.deleteAccountBtn.addEventListener("click", () => this.deleteAccount());
    this.elements.exportDataBtn.addEventListener("click", () => this.exportUserData());
    this.elements.importDataBtn.addEventListener("click", () => this.importUserData());
    this.elements.autoLoginCheckbox.addEventListener("change", () => {
      this.autoLogin = this.elements.autoLoginCheckbox.checked;
      localStorage.setItem("autoLogin", String(this.autoLogin));
      if (this.currentUser) {
        this.saveUserSettings(this.currentUser.id, {
          autoLogin: this.autoLogin,
          rememberPlayback: this.elements.rememberPlaybackCheckbox.checked,
          keepHistory: this.elements.keepHistoryCheckbox.checked
        });
      }
    });
    this.elements.rememberPlaybackCheckbox.addEventListener("change", () => {
      if (this.currentUser) {
        this.saveUserSettings(this.currentUser.id, {
          autoLogin: this.autoLogin,
          rememberPlayback: this.elements.rememberPlaybackCheckbox.checked,
          keepHistory: this.elements.keepHistoryCheckbox.checked
        });
      }
    });
    this.elements.keepHistoryCheckbox.addEventListener("change", () => {
      if (this.currentUser) {
        this.saveUserSettings(this.currentUser.id, {
          autoLogin: this.autoLogin,
          rememberPlayback: this.elements.rememberPlaybackCheckbox.checked,
          keepHistory: this.elements.keepHistoryCheckbox.checked
        });
      }
    });
    this.elements.changeEmailBtn.addEventListener("click", async () => {
      if (this.isGuest) {
        this.showToast("Create an account to set an email address.", "error");
        return;
      }
      const currentEmail = this.currentUser?.email || "";
      const newEmail = prompt("Enter your email address:", currentEmail);
      if (newEmail === null) return;
      const emailInput = newEmail.trim();
      if (!emailInput) {
        this.showToast("Email cannot be empty.", "error");
        return;
      }
      if (!this.isValidEmail(emailInput)) {
        this.showToast("Please enter a valid email address.", "error");
        return;
      }
      if (emailInput.toLowerCase() === currentEmail.toLowerCase()) {
        this.showToast("That is already your email address.", "error");
        return;
      }
      const existingEmail = await this.getUserByEmail(emailInput.toLowerCase());
      if (existingEmail && existingEmail.id !== this.currentUser.id) {
        this.showToast("Another account already uses that email.", "error");
        return;
      }
      const success = await this.updateEmail(emailInput.toLowerCase());
      if (success) {
        this.showToast("Email updated successfully!", "success");
        await this.updateAccountInfo();
        await this.renderUserList();
      } else {
        this.showToast("Failed to update email. Please try again.", "error");
      }
    });
    this.elements.changeUsernameBtn.addEventListener("click", async () => {
      if (this.isGuest) {
        this.showToast("Create an account to change your username.", "error");
        return;
      }
      const currentUsername = this.currentUser?.username || "";
      const newUsername = prompt("Enter your new username:", currentUsername);
      if (newUsername === null) return;
      const usernameInput = newUsername.trim();
      if (!usernameInput) {
        this.showToast("Username cannot be empty.", "error");
        return;
      }
      if (usernameInput.length < 3) {
        this.showToast("Username must be at least 3 characters.", "error");
        return;
      }
      if (usernameInput === currentUsername) {
        this.showToast("That is already your username.", "error");
        return;
      }
      const existingUsername = await this.getUserByUsername(usernameInput);
      if (existingUsername && existingUsername.id !== this.currentUser.id) {
        this.showToast("That username is already taken.", "error");
        return;
      }
      const success = await this.updateUsername(usernameInput);
      if (success) {
        this.showToast("Username updated successfully!", "success");
        await this.updateAccountInfo();
        await this.renderUserList();
      } else {
        this.showToast("Failed to update username. Please try again.", "error");
      }
    });
    this.elements.listUsersBtn.addEventListener("click", async () => {
      const users = await this.getAllUsers();
      this.showUserListModal(users);
    });
    if (this.elements.refreshUsersBtn) {
      this.elements.refreshUsersBtn.addEventListener("click", async () => {
        await this.renderUserList();
        this.showToast("User list refreshed", "success");
      });
    }
    document.getElementById("goto-account-from-music").addEventListener("click", () => {
      this.lastActiveTerminal = "music";
      this.showAccountPage();
    });
    document.getElementById("goto-comedy-from-music")?.addEventListener("click", () => this.showComedyPage());
    document.getElementById("goto-bookmarks-from-music")?.addEventListener("click", () => this.showBookmarksPage());
    document.getElementById("goto-account-from-video").addEventListener("click", () => {
      this.lastActiveTerminal = "video";
      this.showAccountPage();
    });
    document.getElementById("goto-comedy-from-video")?.addEventListener("click", () => this.showComedyPage());
    document.getElementById("goto-bookmarks-from-video")?.addEventListener("click", () => this.showBookmarksPage());
    document.getElementById("goto-account-from-documentary").addEventListener("click", () => {
      this.lastActiveTerminal = "documentary";
      this.showAccountPage();
    });
    document.getElementById("goto-comedy-from-documentary")?.addEventListener("click", () => this.showComedyPage());
    document.getElementById("goto-bookmarks-from-documentary")?.addEventListener("click", () => this.showBookmarksPage());
    document.getElementById("goto-account-from-movie").addEventListener("click", () => {
      this.lastActiveTerminal = "movie";
      this.showAccountPage();
    });
    document.getElementById("goto-comedy-from-movie")?.addEventListener("click", () => this.showComedyPage());
    document.getElementById("goto-bookmarks-from-movie")?.addEventListener("click", () => this.showBookmarksPage());
    document.getElementById("goto-account-from-comedy").addEventListener("click", () => {
      this.lastActiveTerminal = "comedy";
      this.showAccountPage();
    });
    document.getElementById("goto-account-from-webseries").addEventListener("click", () => {
      this.lastActiveTerminal = "webseries";
      this.showAccountPage();
    });
    document.getElementById("goto-comedy-from-webseries")?.addEventListener("click", () => this.showComedyPage());
    document.getElementById("goto-bookmarks-from-webseries")?.addEventListener("click", () => this.showBookmarksPage());
    document.getElementById("goto-account-from-podcast").addEventListener("click", () => {
      this.lastActiveTerminal = "podcast";
      this.showAccountPage();
    });
    document.getElementById("goto-comedy-from-podcast")?.addEventListener("click", () => this.showComedyPage());
    document.getElementById("goto-bookmarks-from-podcast")?.addEventListener("click", () => this.showBookmarksPage());
    document.getElementById("goto-account-from-games").addEventListener("click", () => {
      this.lastActiveTerminal = "games";
      this.showAccountPage();
    });
    document.getElementById("goto-comedy-from-games")?.addEventListener("click", () => this.showComedyPage());
    document.getElementById("goto-bookmarks-from-games")?.addEventListener("click", () => this.showBookmarksPage());
    document.getElementById("goto-account-from-books").addEventListener("click", () => {
      this.lastActiveTerminal = "books";
      this.showAccountPage();
    });
    document.getElementById("goto-comedy-from-books")?.addEventListener("click", () => this.showComedyPage());
    document.getElementById("goto-bookmarks-from-books")?.addEventListener("click", () => this.showBookmarksPage());
    document.getElementById("goto-account-from-bookmarks")?.addEventListener("click", () => {
      this.lastActiveTerminal = "bookmarks";
      this.showAccountPage();
    });
    document.getElementById("goto-account-from-hub").addEventListener("click", () => this.showAccountPage());
    document.getElementById("goto-music-from-account").addEventListener("click", () => this.showMusicPage());
    document.getElementById("goto-video-from-account").addEventListener("click", () => this.showVideoPage());
    document.getElementById("goto-documentary-from-account").addEventListener("click", () => this.showDocumentaryPage());
    document.getElementById("goto-movie-from-account").addEventListener("click", () => this.showMoviePage());
    document.getElementById("goto-comedy-from-account").addEventListener("click", () => this.showComedyPage());
    document.getElementById("goto-webseries-from-account").addEventListener("click", () => this.showWebSeriesPage());
    document.getElementById("goto-podcast-from-account").addEventListener("click", () => this.showPodcastPage());
    document.getElementById("goto-games-from-account").addEventListener("click", () => this.showGamesPage());
    document.getElementById("goto-books-from-account").addEventListener("click", () => this.showBooksPage());
    document.getElementById("goto-bookmarks-from-account")?.addEventListener("click", () => this.showBookmarksPage());
    document.getElementById("goto-hub-from-account").addEventListener("click", () => this.showTerminalHubPage());
    document.getElementById("goto-hub-from-music").addEventListener("click", () => this.showTerminalHubPage());
    document.getElementById("goto-hub-from-video").addEventListener("click", () => this.showTerminalHubPage());
    document.getElementById("goto-hub-from-documentary").addEventListener("click", () => this.showTerminalHubPage());
    document.getElementById("goto-hub-from-movie").addEventListener("click", () => this.showTerminalHubPage());
    document.getElementById("goto-hub-from-comedy").addEventListener("click", () => this.showTerminalHubPage());
    document.getElementById("goto-hub-from-webseries").addEventListener("click", () => this.showTerminalHubPage());
    document.getElementById("goto-hub-from-podcast").addEventListener("click", () => this.showTerminalHubPage());
    document.getElementById("goto-hub-from-games").addEventListener("click", () => this.showTerminalHubPage());
    document.getElementById("goto-hub-from-books").addEventListener("click", () => this.showTerminalHubPage());
    document.getElementById("goto-hub-from-bookmarks")?.addEventListener("click", () => this.showTerminalHubPage());
    document.getElementById("goto-hub-from-gamevideo")?.addEventListener("click", () => this.showTerminalHubPage());
    document.getElementById("goto-hub-from-gamemovie")?.addEventListener("click", () => this.showTerminalHubPage());
    document.getElementById("goto-hub-from-bookvideo")?.addEventListener("click", () => this.showTerminalHubPage());
    document.getElementById("goto-hub-from-bookmovie")?.addEventListener("click", () => this.showTerminalHubPage());
    document.getElementById("goto-hub-from-presentations")?.addEventListener("click", () => this.showTerminalHubPage());
    document.getElementById("goto-account-from-gamevideo")?.addEventListener("click", () => {
      this.lastActiveTerminal = "gamevideo";
      this.showAccountPage();
    });
    document.getElementById("goto-account-from-gamemovie")?.addEventListener("click", () => {
      this.lastActiveTerminal = "gamemovie";
      this.showAccountPage();
    });
    document.getElementById("goto-account-from-bookvideo")?.addEventListener("click", () => {
      this.lastActiveTerminal = "bookvideo";
      this.showAccountPage();
    });
    document.getElementById("goto-account-from-bookmovie")?.addEventListener("click", () => {
      this.lastActiveTerminal = "bookmovie";
      this.showAccountPage();
    });
    document.getElementById("goto-account-from-presentations")?.addEventListener("click", () => {
      this.lastActiveTerminal = "presentations";
      this.showAccountPage();
    });
    const crossNavMap = {
      gamevideo: this.showGameVideoPage,
      gamemovie: this.showGameMoviePage,
      bookvideo: this.showBookVideoPage,
      bookmovie: this.showBookMoviePage,
      music: this.showMusicPage,
      video: this.showVideoPage,
      documentary: this.showDocumentaryPage,
      comedy: this.showComedyPage,
      webseries: this.showWebSeriesPage,
      movie: this.showMoviePage,
      podcast: this.showPodcastPage,
      games: this.showGamesPage,
      books: this.showBooksPage,
      bookmarks: this.showBookmarksPage,
      presentations: this.showPresentationsPage
    };
    [ "gamevideo", "gamemovie", "bookvideo", "bookmovie", "presentations" ].forEach(fromKey => {
      Object.keys(crossNavMap).forEach(toKey => {
        if (toKey === fromKey) return;
        const btn = document.getElementById(`goto-${toKey}-from-${fromKey}`);
        const target = crossNavMap[toKey];
        if (btn && typeof target === "function") {
          btn.addEventListener("click", () => target.call(this));
        }
      });
    });
    document.getElementById("hub-goto-music").addEventListener("click", () => this.showMusicPage());
    document.getElementById("hub-goto-video").addEventListener("click", () => this.showVideoPage());
    document.getElementById("hub-goto-documentary").addEventListener("click", () => this.showDocumentaryPage());
    document.getElementById("hub-goto-movie").addEventListener("click", () => this.showMoviePage());
    document.getElementById("hub-goto-comedy").addEventListener("click", () => this.showComedyPage());
    document.getElementById("goto-music-from-comedy")?.addEventListener("click", () => this.showMusicPage());
    document.getElementById("goto-podcast-from-comedy")?.addEventListener("click", () => this.showPodcastPage());
    document.getElementById("goto-video-from-comedy")?.addEventListener("click", () => this.showVideoPage());
    document.getElementById("goto-documentary-from-comedy")?.addEventListener("click", () => this.showDocumentaryPage());
    document.getElementById("goto-movie-from-comedy")?.addEventListener("click", () => this.showMoviePage());
    document.getElementById("goto-webseries-from-comedy")?.addEventListener("click", () => this.showWebSeriesPage());
    document.getElementById("goto-games-from-comedy")?.addEventListener("click", () => this.showGamesPage());
    document.getElementById("goto-books-from-comedy")?.addEventListener("click", () => this.showBooksPage());
    document.getElementById("goto-bookmarks-from-comedy")?.addEventListener("click", () => this.showBookmarksPage());
    document.getElementById("hub-goto-webseries").addEventListener("click", () => this.showWebSeriesPage());
    document.getElementById("hub-goto-podcast").addEventListener("click", () => this.showPodcastPage());
    document.getElementById("hub-goto-games").addEventListener("click", () => this.showGamesPage());
    document.getElementById("hub-goto-books").addEventListener("click", () => this.showBooksPage());
    document.getElementById("hub-goto-gamevideo").addEventListener("click", () => this.showGameVideoPage());
    document.getElementById("hub-goto-gamemovie").addEventListener("click", () => this.showGameMoviePage());
    document.getElementById("hub-goto-bookvideo").addEventListener("click", () => this.showBookVideoPage());
    document.getElementById("hub-goto-bookmovie").addEventListener("click", () => this.showBookMoviePage());
    document.getElementById("hub-goto-presentations").addEventListener("click", () => this.showPresentationsPage());
    document.getElementById("hub-goto-bookmarks").addEventListener("click", () => this.showBookmarksPage());
    document.getElementById("goto-music-from-bookmarks")?.addEventListener("click", () => this.showMusicPage());
    document.getElementById("goto-podcast-from-bookmarks")?.addEventListener("click", () => this.showPodcastPage());
    document.getElementById("goto-video-from-bookmarks")?.addEventListener("click", () => this.showVideoPage());
    document.getElementById("goto-documentary-from-bookmarks")?.addEventListener("click", () => this.showDocumentaryPage());
    document.getElementById("goto-movie-from-bookmarks")?.addEventListener("click", () => this.showMoviePage());
    document.getElementById("goto-comedy-from-bookmarks")?.addEventListener("click", () => this.showComedyPage());
    document.getElementById("goto-webseries-from-bookmarks")?.addEventListener("click", () => this.showWebSeriesPage());
    document.getElementById("goto-games-from-bookmarks")?.addEventListener("click", () => this.showGamesPage());
    document.getElementById("goto-books-from-bookmarks")?.addEventListener("click", () => this.showBooksPage());
    document.getElementById("login-username").addEventListener("keydown", e => {
      if (e.key === "Enter") this.elements.loginBtn.click();
    });
    document.getElementById("login-password").addEventListener("keydown", e => {
      if (e.key === "Enter") this.elements.loginBtn.click();
    });
    document.getElementById("signup-username").addEventListener("keydown", e => {
      if (e.key === "Enter") document.getElementById("signup-email").focus();
    });
    document.getElementById("signup-email").addEventListener("keydown", e => {
      if (e.key === "Enter") document.getElementById("signup-password").focus();
    });
    document.getElementById("signup-password").addEventListener("keydown", e => {
      if (e.key === "Enter") document.getElementById("signup-confirm").focus();
    });
    document.getElementById("signup-confirm").addEventListener("keydown", e => {
      if (e.key === "Enter") this.elements.signupBtn.click();
    });
    const identifierInput = this.elements.loginIdentifierInput;
    identifierInput.addEventListener("blur", () => {
      const identifier = identifierInput.value.trim();
      checkAndApplyLockoutOnLoad(identifier, this.elements.status, this.elements.loginBtn, this.elements.loginIdentifierInput, this.elements.loginPasswordInput);
    });
    const forgotPasswordLink = document.getElementById("forgot-password-link");
    if (forgotPasswordLink) {
      forgotPasswordLink.addEventListener("click", () => {
        const identifier = forgotPasswordLink.dataset.identifier || this.elements.loginIdentifierInput.value.trim();
        if (!identifier) return;
        document.querySelectorAll(".tab-btn").forEach(t => t.classList.remove("active"));
        document.querySelectorAll(".login-form").forEach(f => f.classList.remove("active"));
        document.getElementById("reset-password-form").classList.add("active");
        document.getElementById("reset-username").value = identifier;
        this.elements.status.textContent = "";
        this.elements.status.classList.remove("status-lockout", "status-success");
      });
    }
    const resetCancelBtn = document.getElementById("reset-password-cancel-btn");
    if (resetCancelBtn) {
      resetCancelBtn.addEventListener("click", () => {
        document.getElementById("reset-password-form").classList.remove("active");
        document.querySelector('.tab-btn[data-tab="signin"]').classList.add("active");
        document.getElementById("signin-form").classList.add("active");
        this.clearLoginFormState();
      });
    }
    const resetSubmitBtn = document.getElementById("reset-password-submit-btn");
    if (resetSubmitBtn) {
      resetSubmitBtn.addEventListener("click", async () => {
        const identifier = document.getElementById("reset-username").value.trim();
        const email = document.getElementById("reset-email").value.trim();
        const passkey = document.getElementById("reset-passkey").value.trim();
        const newPassword = document.getElementById("reset-new-password").value;
        const confirmPassword = document.getElementById("reset-confirm-password").value;
        this.elements.status.classList.remove("status-lockout", "status-success");
        if (!email) {
          this.elements.status.textContent = "Please enter the email on this account.";
          return;
        }
        if (!passkey) {
          this.elements.status.textContent = "Please enter your recovery passkey.";
          return;
        }
        if (!newPassword) {
          this.elements.status.textContent = "Please enter a new password.";
          return;
        }
        if (newPassword !== confirmPassword) {
          this.elements.status.textContent = "Passwords do not match.";
          return;
        }
        const result = await this.resetPasswordForIdentifier(identifier, email, passkey, newPassword);
        this.elements.status.textContent = result.message;
        if (result.success) {
          this.elements.status.classList.add("status-success");
          document.getElementById("reset-password-form").classList.remove("active");
          document.querySelector('.tab-btn[data-tab="signin"]').classList.add("active");
          document.getElementById("signin-form").classList.add("active");
          document.getElementById("login-username").value = identifier;
          document.getElementById("login-password").value = "";
          document.getElementById("reset-passkey").value = "";
          hideForgotPasswordPrompt();
        }
      });
    }
    const resetWithQuestionsLink = document.getElementById("reset-with-security-questions-link");
    if (resetWithQuestionsLink) {
      resetWithQuestionsLink.addEventListener("click", async () => {
        const identifier = document.getElementById("reset-username").value.trim() || this.elements.loginIdentifierInput.value.trim();
        if (!identifier) {
          this.elements.status.textContent = "Enter your username or email first.";
          return;
        }
        const user = await this.findUserByIdentifier(identifier);
        if (!user || !user.securityQuestions || !user.securityQuestions.length) {
          this.elements.status.textContent = "No security questions are set up for this account.";
          return;
        }
        const answered = [];
        for (const q of user.securityQuestions) {
          const answer = prompt(q.question);
          if (answer === null) return;
          answered.push({
            question: q.question,
            answer: answer
          });
        }
        const newPassword = prompt("Answers accepted if correct. Enter a new password (min 6 characters):");
        if (!newPassword) return;
        const confirmPassword = prompt("Confirm new password:");
        if (newPassword !== confirmPassword) {
          alert("Passwords do not match.");
          return;
        }
        const result = await this.resetPasswordWithSecurityAnswers(identifier, answered, newPassword);
        this.elements.status.textContent = result.message;
        if (result.success) {
          this.elements.status.classList.add("status-success");
          document.getElementById("reset-password-form").classList.remove("active");
          document.querySelector('.tab-btn[data-tab="signin"]').classList.add("active");
          document.getElementById("signin-form").classList.add("active");
          document.getElementById("login-username").value = identifier;
          hideForgotPasswordPrompt();
        }
      });
    }
    attachVisibilityToggle(document.getElementById("login-password"), document.getElementById("toggle-login-password"));
    attachVisibilityToggle(document.getElementById("signup-password"), document.getElementById("toggle-signup-password"));
    attachVisibilityToggle(document.getElementById("signup-confirm"), document.getElementById("toggle-signup-confirm"));
    attachVisibilityToggle(document.getElementById("reset-new-password"), document.getElementById("toggle-reset-new-password"));
    attachVisibilityToggle(document.getElementById("signup-passkey"), document.getElementById("toggle-signup-passkey"));
    attachVisibilityToggle(document.getElementById("reset-passkey"), document.getElementById("toggle-reset-passkey"));
    const setSecurityQuestionsBtn = document.getElementById("set-security-questions-btn");
    if (setSecurityQuestionsBtn) {
      setSecurityQuestionsBtn.addEventListener("click", async () => {
        if (this.isGuest || !this.currentUser) {
          this.showToast("Create an account to set security questions.", "error");
          return;
        }
        const bank = novaConfig && novaConfig.securityQuestions && novaConfig.securityQuestions.questionBank || [ "What is your favorite movie?", "What is your favorite food?", "What was the name of your first pet?" ];
        const qaPairs = [];
        for (let i = 0; i < 3; i++) {
          const question = prompt(`Pick a security question ${i + 1} of 3 (or type your own):\n\n${bank.join("\n")}`);
          if (!question) return;
          const answer = prompt(`Your answer for: "${question}"`);
          if (!answer) return;
          qaPairs.push({
            question: question,
            answer: answer
          });
        }
        const ok = await this.setSecurityQuestions(this.currentUser.id, qaPairs);
        alert(ok ? "Security questions saved." : "Failed to save security questions.");
      });
    }
    const setRecoveryPasskeyBtn = document.getElementById("set-recovery-passkey-btn");
    if (setRecoveryPasskeyBtn) {
      setRecoveryPasskeyBtn.addEventListener("click", async () => {
        if (this.isGuest || !this.currentUser) {
          this.showToast("Create an account to set a recovery passkey.", "error");
          return;
        }
        const value = prompt("Set a recovery passkey. Pick any whole number from 0 to 1,000,000,000,000. You will need this if you ever forget your password.");
        if (value === null) return;
        const trimmed = value.trim();
        if (!isValidPasskeyValue(trimmed)) {
          alert("Recovery passkey must be a whole number between 0 and 1,000,000,000,000.");
          return;
        }
        const confirmValue = prompt("Confirm your recovery passkey:");
        if (confirmValue === null) return;
        if (normalizePasskeyValue(trimmed) !== normalizePasskeyValue(confirmValue.trim())) {
          alert("Passkeys do not match.");
          return;
        }
        const ok = await this.setRecoveryPasskey(this.currentUser.id, trimmed);
        alert(ok ? "Recovery passkey saved." : "Failed to save recovery passkey.");
      });
    }
    const exportActivityBtn = document.getElementById("export-account-activity-btn");
    if (exportActivityBtn) {
      exportActivityBtn.addEventListener("click", () => {
        if (this.isGuest || !this.currentUser) {
          this.showToast("Create an account to export activity.", "error");
          return;
        }
        exportAccountActivity(this.currentUser.id, this.currentUser.username);
      });
    }
  }
  isValidEmail(email) {
    return /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email);
  }
  async getUserByEmail(email) {
    return new Promise(resolve => {
      const tx = this.db.transaction("users", "readonly");
      const store = tx.objectStore("users");
      const index = store.index("email");
      const request = index.get(email.toLowerCase());
      request.onsuccess = () => resolve(request.result || null);
      request.onerror = () => resolve(null);
    });
  }
  async findUserByIdentifier(identifier) {
    const trimmed = identifier.trim();
    if (!trimmed) return null;
    const byUsername = await this.getUserByUsername(trimmed);
    if (byUsername) return byUsername;
    if (trimmed.includes("@")) {
      const byEmail = await this.getUserByEmail(trimmed.toLowerCase());
      if (byEmail) return byEmail;
    }
    return null;
  }
  async createAccount(username, email, password, passkey) {
    if (!this.db) {
      this.elements.status.textContent = "Account storage isn't ready yet. Please wait a moment and try again.";
      return false;
    }
    if (username.length < 3) {
      this.elements.status.textContent = "Username must be at least 3 characters.";
      return false;
    }
    if (!email) {
      this.elements.status.textContent = "Email is required.";
      return false;
    }
    if (!this.isValidEmail(email)) {
      this.elements.status.textContent = "Please enter a valid email address.";
      return false;
    }
    if (password.length < 6) {
      this.elements.status.textContent = "Password must be at least 6 characters.";
      return false;
    }
    if (!passkey || !isValidPasskeyValue(passkey)) {
      this.elements.status.textContent = "A valid recovery passkey number (0 to 1,000,000,000,000) is required.";
      return false;
    }
    const existingUsername = await this.getUserByUsername(username);
    if (existingUsername) {
      this.elements.status.textContent = "Username already taken. Please choose another.";
      return false;
    }
    const existingEmail = await this.getUserByEmail(email.toLowerCase());
    if (existingEmail) {
      this.elements.status.textContent = "An account with that email already exists.";
      return false;
    }
    const user = {
      username: username,
      email: email.toLowerCase(),
      passwordHash: await this.hashPassword(password),
      passkeyHash: await this.hashPassword(normalizePasskeyValue(passkey)),
      createdAt: (new Date).toISOString()
    };
    const tx = this.db.transaction("users", "readwrite");
    const store = tx.objectStore("users");
    const request = store.add(user);
    return new Promise((resolve, reject) => {
      request.onsuccess = async () => {
        const userId = request.result;
        await this.saveUserSettings(userId, {
          autoLogin: false,
          rememberPlayback: true,
          keepHistory: true
        });
        logAccountEventForUser(userId, "account_created");
        this.elements.status.textContent = "Account created! Please sign in.";
        resolve(true);
      };
      request.onerror = () => {
        this.elements.status.textContent = "Failed to create account. Please try again.";
        reject(request.error);
      };
    });
  }
  async signIn(identifier, password) {
    if (!this.db) {
      this.elements.status.classList.remove("status-lockout", "status-success");
      this.elements.status.textContent = "Account storage isn't ready yet. Please wait a moment and try again.";
      return false;
    }
    if (checkAndApplyLockoutOnLoad(identifier, this.elements.status, this.elements.loginBtn, this.elements.loginIdentifierInput, this.elements.loginPasswordInput)) {
      return false;
    }
    const user = await this.findUserByIdentifier(identifier);
    const isValid = user ? await this.verifyPassword(password, user.passwordHash) : false;
    if (!user || !isValid) {
      const state = recordFailedAttempt(identifier);
      if (state && state.lockedUntil) {
        startLockoutCountdown(identifier, this.elements.status, this.elements.loginBtn, this.elements.loginIdentifierInput, this.elements.loginPasswordInput);
      } else {
        this.elements.status.classList.remove("status-lockout", "status-success");
        this.elements.status.textContent = "Incorrect username/email or password.";
        if (state && state.attempts >= LOGIN_PASSWORD_PROMPT_AT) {
          this.elements.status.textContent += ` (${state.attempts}/${LOGIN_MAX_ATTEMPTS} attempts) Forgotten it?`;
          showForgotPasswordPrompt(identifier);
        }
      }
      return false;
    }
    clearActiveLockoutIdentifier();
    hideForgotPasswordPrompt();
    const session = await this.createSession(user.id);
    await this.activateUser(user, session.token);
    logAccountEvent(user.id, "login");
    renderAccountActivitySummary(user.id);
    return true;
  }
  async activateUser(user, token) {
    this.currentUser = user;
    this.sessionToken = token;
    this.userId = user.id;
    this.isGuest = false;
    currentUserId = user.id;
    localStorage.setItem("sessionToken", token);
    await loadAllUserMediaData();
    await this.loadUserSettings(user.id);
    await this.updateAccountInfo();
  }
  async continueAsGuest() {
    this.currentUser = {
      id: GUEST_USER_ID,
      username: "Guest",
      email: null,
      createdAt: (new Date).toISOString()
    };
    this.sessionToken = null;
    this.userId = GUEST_USER_ID;
    this.isGuest = true;
    currentUserId = GUEST_USER_ID;
    dismissFirstTimeBanner();
    await loadAllUserMediaData();
    await this.loadUserSettings(GUEST_USER_ID);
    await this.updateAccountInfo();
    this.showTerminalHubPage();
  }
  async signOut() {
    if (this.currentUser && !this.isGuest) {
      logAccountEvent(this.currentUser.id, "logout");
    }
    if (this.sessionToken) {
      await this.deleteSession(this.sessionToken);
      localStorage.removeItem("sessionToken");
    }
    this.currentUser = null;
    this.sessionToken = null;
    this.userId = null;
    this.isGuest = false;
    currentUserId = null;
    resetAllMediaState();
    this.clearLoginFormState();
    this.updateGuestUI();
    this.showLoginPage();
  }
  async changePassword() {
    if (this.isGuest) {
      this.showToast("Create an account to set a password.", "error");
      return;
    }
    const newPass = prompt("Enter new password (min 6 characters):");
    if (!newPass) return;
    if (newPass.length < 6) {
      alert("Password must be at least 6 characters.");
      return;
    }
    const confirm = prompt("Confirm new password:");
    if (newPass !== confirm) {
      alert("Passwords do not match.");
      return;
    }
    const tx = this.db.transaction("users", "readwrite");
    const store = tx.objectStore("users");
    const user = await this.getUserById(this.currentUser.id);
    user.passwordHash = await this.hashPassword(newPass);
    const request = store.put(user);
    request.onsuccess = () => {
      logAccountEvent(user.id, "password_changed");
      alert("Password changed successfully.");
    };
    request.onerror = () => {
      alert("Failed to change password.");
    };
  }
  async resetPasswordForIdentifier(identifier, email, passkey, newPassword) {
    if (isResetLockedOut(identifier)) {
      const state = getResetLockoutState(identifier);
      const secondsLeft = Math.ceil((state.lockedUntil - Date.now()) / 1e3);
      return {
        success: false,
        message: `Too many failed passkey attempts. Please try again in ${secondsLeft} second${secondsLeft === 1 ? "" : "s"}...`
      };
    }
    const user = await this.findUserByIdentifier(identifier);
    if (!user) {
      return {
        success: false,
        message: "No account found with that username or email."
      };
    }
    if (user.email.toLowerCase() !== email.trim().toLowerCase()) {
      return {
        success: false,
        message: "That email does not match the one on this account."
      };
    }
    if (!user.passkeyHash) {
      return {
        success: false,
        message: "No recovery passkey is set on this account. Use security questions instead."
      };
    }
    if (!passkey || !isValidPasskeyValue(passkey)) {
      return {
        success: false,
        message: "Please enter your recovery passkey number."
      };
    }
    const passkeyValid = await this.verifyPassword(normalizePasskeyValue(passkey), user.passkeyHash);
    if (!passkeyValid) {
      const state = recordFailedResetAttempt(identifier);
      if (state && state.lockedUntil) {
        const secondsLeft = Math.ceil((state.lockedUntil - Date.now()) / 1e3);
        return {
          success: false,
          message: `Too many failed passkey attempts. Please try again in ${secondsLeft} second${secondsLeft === 1 ? "" : "s"}...`
        };
      }
      return {
        success: false,
        message: `Incorrect recovery passkey. (${state.attempts}/${RESET_MAX_ATTEMPTS} attempts)`
      };
    }
    if (newPassword.length < 6) {
      return {
        success: false,
        message: "New password must be at least 6 characters."
      };
    }
    user.passwordHash = await this.hashPassword(newPassword);
    const tx = this.db.transaction("users", "readwrite");
    const store = tx.objectStore("users");
    const request = store.put(user);
    return new Promise(resolve => {
      request.onsuccess = () => {
        clearLockoutState(identifier);
        clearActiveLockoutIdentifier();
        clearResetLockoutState(identifier);
        logAccountEventForUser(user.id, "password_reset");
        resolve({
          success: true,
          message: "Password reset. Please sign in with your new password."
        });
      };
      request.onerror = () => {
        resolve({
          success: false,
          message: "Failed to reset password. Please try again."
        });
      };
    });
  }
  async updateEmail(newEmail) {
    if (!this.currentUser) return false;
    try {
      const user = await this.getUserById(this.currentUser.id);
      if (!user) return false;
      user.email = newEmail;
      return new Promise(resolve => {
        const tx = this.db.transaction("users", "readwrite");
        const store = tx.objectStore("users");
        const request = store.put(user);
        request.onsuccess = () => {
          this.currentUser.email = newEmail;
          resolve(true);
        };
        request.onerror = () => {
          console.error("Failed to update email:", request.error);
          resolve(false);
        };
      });
    } catch (err) {
      console.error("Error updating email:", err);
      return false;
    }
  }
  async updateUsername(newUsername) {
    if (!this.currentUser) return false;
    try {
      const user = await this.getUserById(this.currentUser.id);
      if (!user) return false;
      user.username = newUsername;
      return new Promise(resolve => {
        const tx = this.db.transaction("users", "readwrite");
        const store = tx.objectStore("users");
        const request = store.put(user);
        request.onsuccess = () => {
          this.currentUser.username = newUsername;
          resolve(true);
        };
        request.onerror = () => {
          console.error("Failed to update username:", request.error);
          resolve(false);
        };
      });
    } catch (err) {
      console.error("Error updating username:", err);
      return false;
    }
  }
  async deleteAccount() {
    if (this.isGuest) {
      this.showToast("Guest sessions have no account to delete. Sign out to leave guest mode.", "error");
      return;
    }
    if (!confirm("Are you sure you want to delete your account? All data will be permanently lost.")) return;
    if (!confirm("This action cannot be undone. Are you absolutely sure?")) return;
    const userId = this.currentUser.id;
    const tx = this.db.transaction([ "users", "sessions", "settings" ], "readwrite");
    tx.objectStore("users").delete(userId);
    const sessions = tx.objectStore("sessions").index("userId");
    const range = IDBKeyRange.only(userId);
    sessions.openCursor(range).onsuccess = e => {
      const cursor = e.target.result;
      if (cursor) {
        cursor.delete();
        cursor.continue();
      }
    };
    tx.objectStore("settings").delete(userId);
    tx.oncomplete = async () => {
      await deleteAllMediaForUser(userId);
      await appDeleteAllForUser(userId);
      localStorage.removeItem("sessionToken");
      localStorage.removeItem("autoLogin");
      this.currentUser = null;
      this.sessionToken = null;
      this.userId = null;
      currentUserId = null;
      alert("Account deleted successfully.");
      location.reload();
    };
    tx.onerror = () => {
      alert("Failed to delete account.");
    };
  }
  async exportUserData() {
    if (!this.currentUser) return;
    this.showToast("Preparing export… this can take a moment.", "info");
    const zip = new JSZip;
    const MEDIA_TYPES = [ {
      key: "music",
      db: musicDB,
      store: "music",
      hasPositions: true
    }, {
      key: "video",
      db: videoDB,
      store: "videos",
      hasPositions: true
    }, {
      key: "podcast",
      db: podcastDB,
      store: "episodes",
      hasPositions: true
    }, {
      key: "documentary",
      db: documentaryDB,
      store: "documentary",
      hasPositions: true
    }, {
      key: "movie",
      db: movieDB,
      store: "movie",
      hasPositions: true
    }, {
      key: "comedy",
      db: comedyDB,
      store: "comedy",
      hasPositions: true
    }, {
      key: "webseries",
      db: webseriesDB,
      store: "webseries",
      hasPositions: true
    }, {
      key: "games",
      db: gamesDB,
      store: "games",
      hasPositions: false
    }, {
      key: "books",
      db: booksDB,
      store: "books",
      hasPositions: false
    }, {
      key: "gamevideo",
      db: gamevideoDB,
      store: "gamevideo",
      hasPositions: true
    }, {
      key: "gamemovie",
      db: gamemovieDB,
      store: "gamemovie",
      hasPositions: true
    }, {
      key: "bookvideo",
      db: bookvideoDB,
      store: "bookvideo",
      hasPositions: true
    }, {
      key: "bookmovie",
      db: bookmovieDB,
      store: "bookmovie",
      hasPositions: true
    }, {
      key: "presentations",
      db: presentationsDB,
      store: "presentations",
      hasPositions: false
    } ];
    const indexFor = (items, folder) => {
      const usedNames = new Set;
      return items.map(item => {
        const safeName = item.name.replace(/[\\/:*?"<>|]/g, "_");
        let fileName = `${item.id}_${safeName}`;
        while (usedNames.has(fileName)) fileName = `${item.id}_${Math.random().toString(36).slice(2)}_${safeName}`;
        usedNames.add(fileName);
        zip.file(`${folder}/${fileName}`, item.blob);
        return {
          oldId: item.id,
          name: item.name,
          mimeType: item.blob.type,
          file: `${folder}/${fileName}`
        };
      });
    };
    const items = {};
    const playlists = {};
    const playlistMeta = {};
    const positions = {};
    for (const type of MEDIA_TYPES) {
      const mediaItems = type.db ? await getAllUserMedia(type.db, type.store) : [];
      items[type.key] = indexFor(mediaItems, type.key);
      playlists[type.key] = appGet(`${type.key}Playlists`, {});
      playlistMeta[type.key] = appGet(`${type.key}PlaylistMeta`, {});
      if (type.hasPositions) {
        positions[type.key] = appGet(`${type.key}Positions`, {});
      }
    }
    if (podcastDB) {
      playlists.podcast = await new Promise(resolve => {
        const tx = podcastDB.transaction("playlists", "readonly");
        const store = tx.objectStore("playlists");
        const req = store.getAll();
        req.onsuccess = () => {
          const out = {};
          (req.result || []).filter(p => p.userId === this.currentUser.id).forEach(p => {
            out[p.name] = p.songs;
          });
          resolve(out);
        };
        req.onerror = () => resolve({});
      });
    }
    const bookmarksExport = bookmarkDB ? await new Promise(resolve => {
      const tx = bookmarkDB.transaction("bookmarks", "readonly");
      const store = tx.objectStore("bookmarks");
      const req = store.getAll();
      req.onsuccess = () => resolve((req.result || []).filter(b => b.userId === this.currentUser.id));
      req.onerror = () => resolve([]);
    }) : [];
    const manifest = {
      formatVersion: 2,
      user: {
        username: this.currentUser.username,
        email: this.currentUser.email,
        createdAt: this.currentUser.createdAt
      },
      exportedAt: (new Date).toISOString(),
      settings: await this.getUserSettings(this.currentUser.id),
      items: items,
      playlists: playlists,
      playlistMeta: playlistMeta,
      positions: positions,
      bookmarks: bookmarksExport,
      sortModes: appGet(`sortModes:${this.currentUser.id}`, {}),
      trackSortModes: appGet(`trackSortModes:${this.currentUser.id}`, {})
    };
    zip.file("manifest.json", JSON.stringify(manifest));
    const zipBlob = await zip.generateAsync({
      type: "blob"
    });
    const url = URL.createObjectURL(zipBlob);
    const a = document.createElement("a");
    a.href = url;
    a.download = `${this.currentUser.username}_data_${(new Date).toISOString().split("T")[0]}.zip`;
    document.body.appendChild(a);
    a.click();
    a.remove();
    URL.revokeObjectURL(url);
    this.showToast("Export complete — check your downloads.", "success");
  }
  async importUserData() {
    const input = document.createElement("input");
    input.type = "file";
    input.accept = ".zip";
    input.onchange = async e => {
      const file = e.target.files[0];
      if (!file) return;
      try {
        this.showToast("Reading zip file… large archives may take a while.", "info");
        const zip = await loadZipWithRetry(file);
        const manifestEntry = zip.file("manifest.json");
        let data = null;
        if (manifestEntry) {
          try {
            const parsed = JSON.parse(await manifestEntry.async("string"));
            if (parsed && parsed.user && parsed.items) data = parsed;
          } catch {
            data = null;
          }
        }
        if (!data) {
          await this.importGenericZipMedia(zip, file.name);
          return;
        }
        if (!confirm(`Import data for user "${data.user.username}"? This will replace all of your current data.`)) return;
        this.showToast("Importing… this can take a moment.", "info");
        await this.importAllUserData(data, zip);
        this.showToast("Data imported successfully. Reloading your library.", "success");
        await loadAllUserMediaData();
        await this.updateAccountInfo();
      } catch (err) {
        console.error("Import failed:", err);
        this.showToast(isNotReadableError(err) ? describeZipReadError(file, err) : "Failed to import data: " + err.message, "error");
      }
    };
    input.click();
  }
  async importGenericZipMedia(zip, archiveName) {
    if (!this.currentUser) return;
    const EXT_ROUTES = {
      mp3: "music",
      wav: "music",
      m4a: "music",
      flac: "music",
      aac: "music",
      ogg: "music",
      oga: "music",
      opus: "music",
      wma: "music",
      mp4: "video",
      mkv: "video",
      mov: "video",
      webm: "video",
      avi: "video",
      m4v: "video",
      wmv: "video",
      flv: "video",
      pdf: "presentations",
      ppt: "presentations",
      pptx: "presentations",
      html: "games",
      htm: "games",
      epub: "books"
    };
    const ROUTE_TARGETS = {
      music: {
        db: musicDB,
        store: "music"
      },
      video: {
        db: videoDB,
        store: "videos"
      },
      presentations: {
        db: presentationsDB,
        store: "presentations"
      },
      games: {
        db: gamesDB,
        store: "games"
      },
      books: {
        db: booksDB,
        store: "books"
      }
    };
    const entries = Object.values(zip.files).filter(entry => !entry.dir);
    if (!entries.length) {
      this.showToast("This zip file is empty.", "error");
      return;
    }
    if (!confirm(`"${archiveName}" doesn't look like a Prism export. Scan it for media files (music, video, PDFs, PPT/PPTX, games, e-books) and add them to your library instead?`)) return;
    this.showToast(`Scanning ${entries.length} file(s)… large media files may take a while.`, "info");
    const counts = {};
    let skipped = 0;
    let processed = 0;
    for (const entry of entries) {
      const baseName = entry.name.split("/").pop();
      const ext = (baseName.split(".").pop() || "").toLowerCase();
      const routeKey = EXT_ROUTES[ext];
      const route = routeKey ? ROUTE_TARGETS[routeKey] : null;
      processed++;
      if (!route || !route.db) {
        skipped++;
        continue;
      }
      try {
        const blob = await entry.async("blob");
        await new Promise((resolve, reject) => {
          const tx = route.db.transaction(route.store, "readwrite");
          tx.objectStore(route.store).add({
            name: baseName,
            blob: blob,
            userId: this.currentUser.id
          });
          tx.oncomplete = () => resolve();
          tx.onerror = () => reject(tx.error);
        });
        counts[routeKey] = (counts[routeKey] || 0) + 1;
      } catch (err) {
        console.error(`Failed to import ${entry.name} from zip`, err);
        skipped++;
      }
      if (processed % 15 === 0 && processed < entries.length) {
        this.showToast(`Imported ${processed} of ${entries.length} file(s) so far…`, "info");
      }
    }
    await loadAllUserMediaData();
    await this.updateAccountInfo();
    const summary = Object.keys(counts).length ? Object.entries(counts).map(([key, n]) => `${n} ${key}`).join(", ") : "no recognizable media files";
    this.showToast(`Imported ${summary} from "${archiveName}"${skipped ? ` (skipped ${skipped} unsupported file(s))` : ""}.`, Object.keys(counts).length ? "success" : "error");
  }
  async importAllUserData(data, zip) {
    const userId = this.currentUser.id;
    if (data.settings) {
      await this.saveUserSettings(userId, data.settings);
    }
    const MEDIA_TYPES = [ {
      key: "music",
      db: musicDB,
      store: "music",
      hasPositions: true
    }, {
      key: "video",
      db: videoDB,
      store: "videos",
      hasPositions: true
    }, {
      key: "podcast",
      db: podcastDB,
      store: "episodes",
      hasPositions: true
    }, {
      key: "documentary",
      db: documentaryDB,
      store: "documentary",
      hasPositions: true
    }, {
      key: "movie",
      db: movieDB,
      store: "movie",
      hasPositions: true
    }, {
      key: "comedy",
      db: comedyDB,
      store: "comedy",
      hasPositions: true
    }, {
      key: "webseries",
      db: webseriesDB,
      store: "webseries",
      hasPositions: true
    }, {
      key: "games",
      db: gamesDB,
      store: "games",
      hasPositions: false
    }, {
      key: "books",
      db: booksDB,
      store: "books",
      hasPositions: false
    }, {
      key: "gamevideo",
      db: gamevideoDB,
      store: "gamevideo",
      hasPositions: true
    }, {
      key: "gamemovie",
      db: gamemovieDB,
      store: "gamemovie",
      hasPositions: true
    }, {
      key: "bookvideo",
      db: bookvideoDB,
      store: "bookvideo",
      hasPositions: true
    }, {
      key: "bookmovie",
      db: bookmovieDB,
      store: "bookmovie",
      hasPositions: true
    }, {
      key: "presentations",
      db: presentationsDB,
      store: "presentations",
      hasPositions: false
    } ];
    const loadItems = async (list, folder) => {
      const out = [];
      for (const entry of list || []) {
        const zipEntry = zip.file(entry.file);
        if (!zipEntry) continue;
        const blob = await zipEntry.async("blob");
        const typedBlob = entry.mimeType ? new Blob([ blob ], {
          type: entry.mimeType
        }) : blob;
        out.push({
          oldId: entry.oldId,
          name: entry.name,
          blob: typedBlob
        });
      }
      return out;
    };
    const remapPlaylists = (playlistsObj, idMap) => {
      const remapped = {};
      Object.keys(playlistsObj || {}).forEach(name => {
        remapped[name] = (playlistsObj[name] || []).map(oldId => idMap.get(oldId)).filter(id => id !== undefined);
      });
      return remapped;
    };
    const remapPositions = (positionsObj, idMap) => {
      const remapped = {};
      Object.keys(positionsObj || {}).forEach(oldId => {
        const newId = idMap.get(Number(oldId));
        if (newId !== undefined) remapped[newId] = positionsObj[oldId];
      });
      return remapped;
    };
    const items = data.items || {};
    const playlists = data.playlists || {};
    const playlistMeta = data.playlistMeta || {};
    const positions = data.positions || {};
    for (const type of MEDIA_TYPES) {
      const typeItems = await loadItems(items[type.key], type.key);
      const idMap = type.db ? await replaceUserMedia(type.db, type.store, typeItems) : new Map;
      if (type.key === "podcast" && podcastDB) {
        const remappedPodcastPlaylists = remapPlaylists(playlists.podcast, idMap);
        await new Promise(resolve => {
          const tx = podcastDB.transaction("playlists", "readwrite");
          const store = tx.objectStore("playlists");
          const getAllReq = store.getAll();
          getAllReq.onsuccess = () => {
            getAllReq.result.filter(p => p.userId === userId).forEach(p => store.delete(p.name));
            Object.keys(remappedPodcastPlaylists).forEach(name => {
              store.put({
                name: name,
                songs: remappedPodcastPlaylists[name],
                userId: userId
              });
            });
          };
          tx.oncomplete = () => resolve();
          tx.onerror = () => resolve();
        });
      } else {
        appSet(`${type.key}Playlists`, remapPlaylists(playlists[type.key], idMap));
      }
      appSet(`${type.key}PlaylistMeta`, playlistMeta[type.key] || {});
      if (type.hasPositions) {
        appSet(`${type.key}Positions`, remapPositions(positions[type.key], idMap));
      }
    }
    if (data.sortModes) appSet(`sortModes:${userId}`, data.sortModes);
    if (data.trackSortModes) appSet(`trackSortModes:${userId}`, data.trackSortModes);
    if (bookmarkDB && Array.isArray(data.bookmarks)) {
      await new Promise(resolve => {
        const tx = bookmarkDB.transaction("bookmarks", "readwrite");
        const store = tx.objectStore("bookmarks");
        const getAllReq = store.getAll();
        getAllReq.onsuccess = () => {
          getAllReq.result.filter(b => b.userId === userId).forEach(b => store.delete(b.id));
          data.bookmarks.forEach(b => {
            store.add({
              title: b.title,
              url: b.url,
              notes: b.notes || "",
              userId: userId,
              createdAt: b.createdAt || Date.now()
            });
          });
        };
        tx.oncomplete = () => resolve();
        tx.onerror = () => resolve();
      });
    }
  }
  async createSession(userId) {
    const token = "sess_" + Date.now() + "_" + Math.random().toString(36).substr(2, 9);
    const session = {
      token: token,
      userId: userId,
      createdAt: (new Date).toISOString(),
      expiresAt: new Date(Date.now() + 7 * 24 * 60 * 60 * 1e3).toISOString()
    };
    const tx = this.db.transaction("sessions", "readwrite");
    const store = tx.objectStore("sessions");
    store.add(session);
    return session;
  }
  async validateSession(token) {
    return new Promise(resolve => {
      const tx = this.db.transaction("sessions", "readonly");
      const store = tx.objectStore("sessions");
      const request = store.get(token);
      request.onsuccess = async () => {
        const session = request.result;
        if (!session) return resolve(null);
        if (new Date(session.expiresAt) < new Date) {
          this.deleteSession(token);
          return resolve(null);
        }
        const user = await this.getUserById(session.userId);
        resolve(user ? {
          user: user,
          session: session
        } : null);
      };
      request.onerror = () => resolve(null);
    });
  }
  async deleteSession(token) {
    const tx = this.db.transaction("sessions", "readwrite");
    tx.objectStore("sessions").delete(token);
  }
  async getUserByUsername(username) {
    return new Promise(resolve => {
      const tx = this.db.transaction("users", "readonly");
      const store = tx.objectStore("users");
      const index = store.index("username");
      const request = index.get(username);
      request.onsuccess = () => resolve(request.result);
      request.onerror = () => resolve(null);
    });
  }
  async getUserById(id) {
    return new Promise(resolve => {
      const tx = this.db.transaction("users", "readonly");
      const store = tx.objectStore("users");
      const request = store.get(id);
      request.onsuccess = () => resolve(request.result);
      request.onerror = () => resolve(null);
    });
  }
  async getTotalUsers() {
    return new Promise(resolve => {
      const tx = this.db.transaction("users", "readonly");
      const store = tx.objectStore("users");
      const count = store.count();
      count.onsuccess = () => resolve(count.result);
      count.onerror = () => resolve(0);
    });
  }
  async getActiveSessions() {
    return new Promise(resolve => {
      const tx = this.db.transaction("sessions", "readonly");
      const store = tx.objectStore("sessions");
      const now = (new Date).toISOString();
      const range = IDBKeyRange.upperBound(now);
      const index = store.index("expiresAt");
      const count = index.count(range);
      count.onsuccess = () => resolve(count.result);
      count.onerror = () => resolve(0);
    });
  }
  async getAllUsers() {
    return new Promise(resolve => {
      const tx = this.db.transaction("users", "readonly");
      const store = tx.objectStore("users");
      const request = store.getAll();
      request.onsuccess = () => resolve(request.result);
      request.onerror = () => resolve([]);
    });
  }
  showUserListModal(users) {
    const existingModal = document.querySelector(".user-list-modal");
    if (existingModal) existingModal.remove();
    const modal = document.createElement("div");
    modal.className = "user-list-modal show";
    const content = document.createElement("div");
    content.className = "user-list-content";
    const closeBtn = document.createElement("button");
    closeBtn.className = "close-modal-btn";
    closeBtn.textContent = "✕";
    closeBtn.addEventListener("click", () => modal.remove());
    const title = document.createElement("h3");
    title.textContent = `👥 All Users (${users.length})`;
    const list = document.createElement("div");
    list.style.maxHeight = "400px";
    list.style.overflowY = "auto";
    if (users.length === 0) {
      const empty = document.createElement("p");
      empty.textContent = "No users found.";
      empty.style.textAlign = "center";
      empty.style.color = "var(--text-secondary)";
      list.appendChild(empty);
    } else {
      users.forEach(user => {
        const item = document.createElement("div");
        item.className = "user-list-item";
        const info = document.createElement("div");
        const name = document.createElement("div");
        name.className = "user-name";
        name.textContent = user.username;
        if (user.id === this.currentUser?.id) {
          const badge = document.createElement("span");
          badge.style.cssText = "font-size:10px;background:var(--accent-cyan);color:#000;padding:2px 8px;border-radius:10px;margin-left:8px;font-weight:700;";
          badge.textContent = "YOU";
          name.appendChild(badge);
        }
        const email = document.createElement("div");
        email.className = "user-email";
        email.textContent = user.email || "No email";
        info.appendChild(name);
        info.appendChild(email);
        const meta = document.createElement("div");
        meta.className = "user-meta";
        const joined = document.createElement("span");
        joined.textContent = `Joined: ${new Date(user.createdAt).toLocaleDateString()}`;
        meta.appendChild(joined);
        item.appendChild(info);
        item.appendChild(meta);
        list.appendChild(item);
      });
    }
    content.appendChild(closeBtn);
    content.appendChild(title);
    content.appendChild(list);
    modal.appendChild(content);
    document.body.appendChild(modal);
    modal.addEventListener("click", e => {
      if (e.target === modal) modal.remove();
    });
  }
  async hashPassword(password, existingSalt) {
    const encoder = new TextEncoder;
    const saltBytes = existingSalt ? Uint8Array.from(atob(existingSalt), c => c.charCodeAt(0)) : crypto.getRandomValues(new Uint8Array(16));
    const passBytes = encoder.encode(password);
    const combined = new Uint8Array(saltBytes.length + passBytes.length);
    combined.set(saltBytes);
    combined.set(passBytes, saltBytes.length);
    const hash = await crypto.subtle.digest("SHA-256", combined);
    const saltB64 = btoa(String.fromCharCode(...saltBytes));
    const hashB64 = btoa(String.fromCharCode(...new Uint8Array(hash)));
    return `${saltB64}:${hashB64}`;
  }
  async verifyPassword(password, storedHash) {
    const [saltB64] = storedHash.split(":");
    const hashed = await this.hashPassword(password, saltB64);
    return hashed === storedHash;
  }
  async setRecoveryPasskey(userId, passkey) {
    const user = await this.getUserById(userId);
    if (!user) return false;
    user.passkeyHash = await this.hashPassword(normalizePasskeyValue(passkey));
    return new Promise(resolve => {
      const tx = this.db.transaction("users", "readwrite");
      const store = tx.objectStore("users");
      const request = store.put(user);
      request.onsuccess = () => resolve(true);
      request.onerror = () => resolve(false);
    });
  }
  normalizeSecurityAnswer(answer) {
    return String(answer || "").trim().toLowerCase().replace(/[^\w\s]/g, "").replace(/\s+/g, " ");
  }
  async setSecurityQuestions(userId, qaPairs) {
    const user = await this.getUserById(userId);
    if (!user) return false;
    const hashed = [];
    for (const qa of qaPairs) {
      const normalized = this.normalizeSecurityAnswer(qa.answer);
      hashed.push({
        question: qa.question,
        answerHash: await this.hashPassword(normalized)
      });
    }
    user.securityQuestions = hashed;
    return new Promise(resolve => {
      const tx = this.db.transaction("users", "readwrite");
      const store = tx.objectStore("users");
      const request = store.put(user);
      request.onsuccess = () => {
        logAccountEvent(userId, "security_questions_set");
        resolve(true);
      };
      request.onerror = () => resolve(false);
    });
  }
  async verifySecurityAnswers(identifier, answeredQaPairs) {
    const user = await this.findUserByIdentifier(identifier);
    if (!user || !user.securityQuestions || !user.securityQuestions.length) {
      return {
        success: false,
        user: null,
        message: "No security questions are set up for this account."
      };
    }
    const required = novaConfig && novaConfig.securityQuestions && novaConfig.securityQuestions.requiredCorrectAnswers || 2;
    let correctCount = 0;
    for (const answered of answeredQaPairs) {
      const stored = user.securityQuestions.find(q => q.question === answered.question);
      if (!stored) continue;
      const normalized = this.normalizeSecurityAnswer(answered.answer);
      const isMatch = await this.verifyPassword(normalized, stored.answerHash);
      if (isMatch) correctCount++;
    }
    if (correctCount < required) {
      return {
        success: false,
        user: null,
        message: `At least ${required} answers must be correct.`
      };
    }
    return {
      success: true,
      user: user,
      message: "Verified."
    };
  }
  async resetPasswordWithSecurityAnswers(identifier, answeredQaPairs, newPassword) {
    if (checkAndApplyLockoutOnLoad(identifier, this.elements.status, this.elements.loginBtn, this.elements.loginIdentifierInput, this.elements.loginPasswordInput)) {
      return {
        success: false,
        message: "Too many attempts. Please wait before trying again."
      };
    }
    const verification = await this.verifySecurityAnswers(identifier, answeredQaPairs);
    if (!verification.success) {
      recordFailedAttempt(identifier);
      return {
        success: false,
        message: verification.message
      };
    }
    if (newPassword.length < (novaConfig && novaConfig.auth && novaConfig.auth.minPasswordLength || 6)) {
      return {
        success: false,
        message: "New password must be at least 6 characters."
      };
    }
    const user = verification.user;
    user.passwordHash = await this.hashPassword(newPassword);
    return new Promise(resolve => {
      const tx = this.db.transaction("users", "readwrite");
      const store = tx.objectStore("users");
      const request = store.put(user);
      request.onsuccess = () => {
        clearLockoutState(identifier);
        clearActiveLockoutIdentifier();
        logAccountEventForUser(user.id, "security_reset_used");
        resolve({
          success: true,
          message: "Password reset. Please sign in with your new password."
        });
      };
      request.onerror = () => resolve({
        success: false,
        message: "Failed to reset password. Please try again."
      });
    });
  }
  generateToken() {
    const bytes = crypto.getRandomValues(new Uint8Array(18));
    const random = Array.from(bytes, b => b.toString(36).padStart(2, "0")).join("");
    return "sess_" + Date.now() + "_" + random;
  }
  async saveUserSettings(userId, settings) {
    const tx = this.db.transaction("settings", "readwrite");
    const store = tx.objectStore("settings");
    store.put({
      userId: userId,
      ...settings
    });
  }
  async getUserSettings(userId) {
    return new Promise(resolve => {
      const tx = this.db.transaction("settings", "readonly");
      const store = tx.objectStore("settings");
      const request = store.get(userId);
      request.onsuccess = () => resolve(request.result || {});
      request.onerror = () => resolve({});
    });
  }
  async loadUserSettings(userId) {
    const settings = await this.getUserSettings(userId);
    if (settings) {
      this.elements.autoLoginCheckbox.checked = settings.autoLogin || false;
      this.elements.rememberPlaybackCheckbox.checked = settings.rememberPlayback !== false;
      this.elements.keepHistoryCheckbox.checked = settings.keepHistory !== false;
      this.autoLogin = settings.autoLogin || false;
      localStorage.setItem("autoLogin", String(this.autoLogin));
    }
  }
  async updateAccountInfo() {
    if (!this.currentUser) return;
    const usernameEl = document.getElementById("account-username");
    const emailEl = document.getElementById("account-email");
    const createdEl = document.getElementById("account-created");
    const mediaCountEl = document.getElementById("account-media-count");
    const storageEl = document.getElementById("account-storage");
    if (usernameEl) {
      usernameEl.textContent = this.currentUser.username;
    }
    if (emailEl) {
      emailEl.textContent = this.currentUser.email || "Not set";
    }
    if (createdEl) createdEl.textContent = new Date(this.currentUser.createdAt).toLocaleDateString();
    if (!this.isGuest) renderAccountActivitySummary(this.currentUser.id);
    const counts = this.getMediaCounts();
    if (mediaCountEl) {
      const total = counts.music + counts.videos + counts.podcasts + counts.documentaries + counts.movies + counts.comedy + counts.webseries + counts.games + counts.books + counts.bookmarks;
      mediaCountEl.textContent = `${total} (${counts.music} music, ${counts.videos} videos, ${counts.podcasts} podcasts, ${counts.documentaries} documentaries, ${counts.movies} movies, ${counts.comedy} comedy, ${counts.webseries} web series, ${counts.games} games, ${counts.books} books, ${counts.bookmarks} bookmarks)`;
    }
    if (storageEl) storageEl.textContent = this.getStorageUsage();
    const totalUsers = await this.getTotalUsers();
    const activeSessions = await this.getActiveSessions();
    const totalUsersEl = document.getElementById("total-users-count");
    const activeSessionsEl = document.getElementById("active-sessions-count");
    if (totalUsersEl) totalUsersEl.textContent = totalUsers;
    if (activeSessionsEl) activeSessionsEl.textContent = activeSessions;
    this.updateGuestUI();
  }
  updateGuestUI() {
    const guestTag = document.getElementById("guest-mode-tag");
    if (guestTag) guestTag.style.display = this.isGuest ? "inline-block" : "none";
    const guestBanner = document.getElementById("guest-account-banner");
    if (guestBanner) guestBanner.style.display = this.isGuest ? "flex" : "none";
  }
  getMediaCounts() {
    return {
      music: music ? music.length : 0,
      videos: videos ? videos.length : 0,
      podcasts: podcasts ? podcasts.length : 0,
      documentaries: documentary ? documentary.length : 0,
      movies: movie ? movie.length : 0,
      comedy: comedy ? comedy.length : 0,
      webseries: webseries ? webseries.length : 0,
      games: games ? games.length : 0,
      books: books ? books.length : 0,
      bookmarks: bookmarks ? bookmarks.length : 0,
      gamevideo: gamevideo ? gamevideo.length : 0,
      gamemovie: gamemovie ? gamemovie.length : 0,
      bookvideo: bookvideo ? bookvideo.length : 0,
      bookmovie: bookmovie ? bookmovie.length : 0,
      presentations: presentations ? presentations.length : 0
    };
  }
  getStorageUsage() {
    let total = 0;
    if (music) music.forEach(s => total += s.blob?.size || 0);
    if (videos) videos.forEach(v => total += v.blob?.size || 0);
    if (podcasts) podcasts.forEach(p => total += p.blob?.size || 0);
    if (documentary) documentary.forEach(v => total += v.blob?.size || 0);
    if (movie) movie.forEach(v => total += v.blob?.size || 0);
    if (comedy) comedy.forEach(v => total += v.blob?.size || 0);
    if (webseries) webseries.forEach(v => total += v.blob?.size || 0);
    if (games) games.forEach(g => total += g.blob?.size || 0);
    if (books) books.forEach(b => total += b.blob?.size || 0);
    if (gamevideo) gamevideo.forEach(v => total += v.blob?.size || 0);
    if (gamemovie) gamemovie.forEach(v => total += v.blob?.size || 0);
    if (bookvideo) bookvideo.forEach(v => total += v.blob?.size || 0);
    if (bookmovie) bookmovie.forEach(v => total += v.blob?.size || 0);
    if (presentations) presentations.forEach(p => total += p.blob?.size || 0);
    if (total < 1024) return total + " B";
    if (total < 1048576) return (total / 1024).toFixed(1) + " KB";
    if (total < 1073741824) return (total / 1048576).toFixed(1) + " MB";
    return (total / 1073741824).toFixed(2) + " GB";
  }
  showLoginPage() {
    showPage("login");
  }
  showTerminalHubPage() {
    showPage("terminal-hub");
  }
  showMusicPage() {
    this.lastActiveTerminal = "music";
    showPage("music");
    this.updateAccountInfo();
  }
  showVideoPage() {
    this.lastActiveTerminal = "video";
    showPage("video");
    this.updateAccountInfo();
  }
  showDocumentaryPage() {
    this.lastActiveTerminal = "documentary";
    showPage("documentary");
    this.updateAccountInfo();
  }
  showMoviePage() {
    this.lastActiveTerminal = "movie";
    showPage("movie");
    this.updateAccountInfo();
  }
  showComedyPage() {
    this.lastActiveTerminal = "comedy";
    showPage("comedy");
    this.updateAccountInfo();
  }
  showBookmarksPage() {
    this.lastActiveTerminal = "bookmarks";
    showPage("bookmarks");
    this.updateAccountInfo();
  }
  showWebSeriesPage() {
    this.lastActiveTerminal = "webseries";
    showPage("webseries");
    this.updateAccountInfo();
  }
  showPodcastPage() {
    this.lastActiveTerminal = "podcast";
    showPage("podcast");
    this.updateAccountInfo();
  }
  showGamesPage() {
    this.lastActiveTerminal = "games";
    showPage("games");
    this.updateAccountInfo();
  }
  showBooksPage() {
    this.lastActiveTerminal = "books";
    showPage("books");
    this.updateAccountInfo();
  }
  showGameVideoPage() {
    this.lastActiveTerminal = "gamevideo";
    showPage("gamevideo");
    this.updateAccountInfo();
  }
  showGameMoviePage() {
    this.lastActiveTerminal = "gamemovie";
    showPage("gamemovie");
    this.updateAccountInfo();
  }
  showBookVideoPage() {
    this.lastActiveTerminal = "bookvideo";
    showPage("bookvideo");
    this.updateAccountInfo();
  }
  showBookMoviePage() {
    this.lastActiveTerminal = "bookmovie";
    showPage("bookmovie");
    this.updateAccountInfo();
  }
  showPresentationsPage() {
    this.lastActiveTerminal = "presentations";
    showPage("presentations");
    this.updateAccountInfo();
  }
  showAccountPage() {
    showPage("account");
    this.updateAccountInfo();
    this.renderUserList();
  }
  getCurrentUserId() {
    return this.userId;
  }
  isLoggedIn() {
    return this.currentUser !== null;
  }
  async deleteUserById(userId) {
    if (!this.currentUser) return {
      success: false,
      message: "Not logged in"
    };
    if (this.currentUser.id === userId) {
      return {
        success: false,
        message: 'Cannot delete your own account. Use the "Delete Account" button instead.'
      };
    }
    const user = await this.getUserById(userId);
    if (!user) {
      return {
        success: false,
        message: "User not found"
      };
    }
    if (!confirm(`Are you sure you want to delete user "${user.username}"? This cannot be undone.`)) {
      return {
        success: false,
        message: "Deletion cancelled"
      };
    }
    try {
      const tx = this.db.transaction([ "users", "sessions", "settings" ], "readwrite");
      tx.objectStore("users").delete(userId);
      const sessions = tx.objectStore("sessions").index("userId");
      const range = IDBKeyRange.only(userId);
      sessions.openCursor(range).onsuccess = e => {
        const cursor = e.target.result;
        if (cursor) {
          cursor.delete();
          cursor.continue();
        }
      };
      tx.objectStore("settings").delete(userId);
      return new Promise(resolve => {
        tx.oncomplete = async () => {
          await deleteAllMediaForUser(userId);
          await appDeleteAllForUser(userId);
          resolve({
            success: true,
            message: `User "${user.username}" deleted successfully.`
          });
        };
        tx.onerror = () => {
          resolve({
            success: false,
            message: "Failed to delete user. Please try again."
          });
        };
      });
    } catch (err) {
      console.error("Error deleting user:", err);
      return {
        success: false,
        message: "An error occurred while deleting the user."
      };
    }
  }
  async renderUserList() {
    const container = document.getElementById("user-list-body");
    if (!container) return;
    const users = await this.getAllUsers();
    if (users.length === 0) {
      container.innerHTML = `\n        <div class="user-list-empty">\n          <span>👤</span>\n          No users found\n        </div>\n      `;
      return;
    }
    container.innerHTML = "";
    users.forEach(user => {
      const isCurrentUser = this.currentUser && user.id === this.currentUser.id;
      const item = document.createElement("div");
      item.className = "user-list-item";
      item.dataset.userId = user.id;
      const nameDisplay = document.createElement("div");
      nameDisplay.className = "user-name-display";
      nameDisplay.appendChild(document.createTextNode(user.username));
      if (isCurrentUser) {
        const badge = document.createElement("span");
        badge.className = "you-badge";
        badge.textContent = "You";
        nameDisplay.appendChild(badge);
      }
      const emailDisplay = document.createElement("div");
      emailDisplay.className = "user-email-display";
      emailDisplay.textContent = user.email || "No email";
      const actions = document.createElement("div");
      actions.className = "user-actions";
      const deleteBtn = document.createElement("button");
      deleteBtn.className = "delete-user-btn";
      deleteBtn.dataset.userId = user.id;
      if (isCurrentUser) deleteBtn.disabled = true;
      deleteBtn.textContent = isCurrentUser ? "✕" : "🗑 Delete";
      actions.appendChild(deleteBtn);
      item.appendChild(nameDisplay);
      item.appendChild(emailDisplay);
      item.appendChild(actions);
      container.appendChild(item);
    });
    container.querySelectorAll(".delete-user-btn").forEach(btn => {
      btn.addEventListener("click", async e => {
        e.stopPropagation();
        const userId = Number(btn.dataset.userId);
        if (!userId) return;
        btn.disabled = true;
        btn.textContent = "⏳";
        const result = await this.deleteUserById(userId);
        if (result.success) {
          this.showToast(result.message, "success");
          await this.renderUserList();
          await this.updateAccountInfo();
          const totalUsers = await this.getTotalUsers();
          const totalUsersEl = document.getElementById("total-users-count");
          if (totalUsersEl) totalUsersEl.textContent = totalUsers;
        } else {
          this.showToast(result.message, "error");
          btn.disabled = false;
          btn.textContent = "🗑 Delete";
        }
      });
    });
  }
  showToast(message, type = "info") {
    const existingToast = document.querySelector(".user-toast");
    if (existingToast) existingToast.remove();
    const toast = document.createElement("div");
    toast.className = `user-toast ${type}`;
    toast.textContent = message;
    document.body.appendChild(toast);
    requestAnimationFrame(() => {
      toast.classList.add("show");
    });
    setTimeout(() => {
      toast.classList.remove("show");
      setTimeout(() => toast.remove(), 500);
    }, 3e3);
  }
}

const pages = {
  login: document.getElementById("login-page"),
  "terminal-hub": document.getElementById("terminal-hub-page"),
  account: document.getElementById("account-page"),
  music: document.getElementById("music-page"),
  video: document.getElementById("video-page"),
  documentary: document.getElementById("documentary-page"),
  movie: document.getElementById("movie-page"),
  comedy: document.getElementById("comedy-page"),
  bookmarks: document.getElementById("bookmarks-page"),
  webseries: document.getElementById("webseries-page"),
  podcast: document.getElementById("podcast-page"),
  games: document.getElementById("games-page"),
  books: document.getElementById("books-page"),
  gamevideo: document.getElementById("gamevideo-page"),
  gamemovie: document.getElementById("gamemovie-page"),
  bookvideo: document.getElementById("bookvideo-page"),
  bookmovie: document.getElementById("bookmovie-page"),
  presentations: document.getElementById("presentations-page")
};

let onPageChange = null;

function showPage(name) {
  Object.values(pages).forEach(p => p.classList.remove("active"));
  if (pages[name]) {
    pages[name].classList.add("active");
    pages[name].setAttribute("aria-hidden", "false");
  }
  Object.keys(pages).filter(k => k !== name).forEach(k => {
    if (pages[k]) pages[k].setAttribute("aria-hidden", "true");
  });
  if (onPageChange) onPageChange(name);
}

let userAccount = null;

const body = document.body;

const activePipBodies = new Set;

function syncPipBodies() {
  const isLight = body.classList.contains("light-mode");
  const isRgb = body.classList.contains("bg-rgb");
  activePipBodies.forEach(b => {
    b.classList.toggle("light-mode", isLight);
    b.classList.toggle("bg-rgb", isRgb);
  });
}

function enableLightMode() {
  body.classList.add("light-mode");
  syncPipBodies();
}

function enableDarkMode() {
  body.classList.remove("light-mode");
  syncPipBodies();
}

const supportsDocPip = "documentPictureInPicture" in window;

function copyStylesInto(targetDoc) {
  [ ...document.styleSheets ].forEach(sheet => {
    try {
      const rules = [ ...sheet.cssRules ].map(r => r.cssText).join("\n");
      const style = targetDoc.createElement("style");
      style.textContent = rules;
      targetDoc.head.appendChild(style);
    } catch {
      if (sheet.href) {
        const link = targetDoc.createElement("link");
        link.rel = "stylesheet";
        link.href = sheet.href;
        targetDoc.head.appendChild(link);
      }
    }
  });
  const baseStyle = targetDoc.createElement("style");
  baseStyle.textContent = "html,body{height:100%;margin:0;background:transparent;font-family:Inter,system-ui,sans-serif;}body{display:flex;}";
  targetDoc.head.appendChild(baseStyle);
}

async function openDocPip(panel, home, onClose, width, height) {
  const pipWindow = await documentPictureInPicture.requestWindow({
    width: width,
    height: height
  });
  copyStylesInto(pipWindow.document);
  pipWindow.document.body.classList.toggle("light-mode", body.classList.contains("light-mode"));
  pipWindow.document.body.classList.toggle("bg-rgb", body.classList.contains("bg-rgb"));
  activePipBodies.add(pipWindow.document.body);
  panel.classList.add("show", "pip-mode");
  pipWindow.document.body.appendChild(panel);
  pipWindow.addEventListener("pagehide", () => {
    activePipBodies.delete(pipWindow.document.body);
    panel.classList.remove("pip-mode");
    home.appendChild(panel);
    onClose();
  }, {
    once: true
  });
  return pipWindow;
}

document.getElementById("music-light-mode").addEventListener("click", enableLightMode);

document.getElementById("music-dark-mode").addEventListener("click", enableDarkMode);

document.getElementById("video-light-mode").addEventListener("click", enableLightMode);

document.getElementById("video-dark-mode").addEventListener("click", enableDarkMode);

document.getElementById("documentary-light-mode").addEventListener("click", enableLightMode);

document.getElementById("documentary-dark-mode").addEventListener("click", enableDarkMode);

document.getElementById("movie-light-mode").addEventListener("click", enableLightMode);

document.getElementById("movie-dark-mode").addEventListener("click", enableDarkMode);

document.getElementById("comedy-light-mode").addEventListener("click", enableLightMode);

document.getElementById("comedy-dark-mode").addEventListener("click", enableDarkMode);

document.getElementById("bookmarks-light-mode").addEventListener("click", enableLightMode);

document.getElementById("bookmarks-dark-mode").addEventListener("click", enableDarkMode);

document.getElementById("webseries-light-mode").addEventListener("click", enableLightMode);

document.getElementById("webseries-dark-mode").addEventListener("click", enableDarkMode);

document.getElementById("podcast-light-mode").addEventListener("click", enableLightMode);

document.getElementById("podcast-dark-mode").addEventListener("click", enableDarkMode);

document.getElementById("games-light-mode").addEventListener("click", enableLightMode);

document.getElementById("games-dark-mode").addEventListener("click", enableDarkMode);

document.getElementById("books-light-mode").addEventListener("click", enableLightMode);

document.getElementById("books-dark-mode").addEventListener("click", enableDarkMode);

document.getElementById("hub-light-mode").addEventListener("click", enableLightMode);

document.getElementById("hub-dark-mode").addEventListener("click", enableDarkMode);

document.getElementById("account-light-mode").addEventListener("click", enableLightMode);

document.getElementById("account-dark-mode").addEventListener("click", enableDarkMode);

document.getElementById("gamevideo-light-mode").addEventListener("click", enableLightMode);

document.getElementById("gamevideo-dark-mode").addEventListener("click", enableDarkMode);

document.getElementById("gamemovie-light-mode").addEventListener("click", enableLightMode);

document.getElementById("gamemovie-dark-mode").addEventListener("click", enableDarkMode);

document.getElementById("bookvideo-light-mode").addEventListener("click", enableLightMode);

document.getElementById("bookvideo-dark-mode").addEventListener("click", enableDarkMode);

document.getElementById("bookmovie-light-mode").addEventListener("click", enableLightMode);

document.getElementById("bookmovie-dark-mode").addEventListener("click", enableDarkMode);

document.getElementById("presentations-light-mode").addEventListener("click", enableLightMode);

document.getElementById("presentations-dark-mode").addEventListener("click", enableDarkMode);

const BACKGROUND_COLOR_STORAGE_KEY = "prismBackgroundColor";
const LEGACY_BACKGROUND_COLOR_STORAGE_KEY = "lumosphereBackgroundColor";

const ccpRoot = document.getElementById("custom-color-picker");

const ccpSwatch = document.getElementById("custom-color-picker-swatch");

const ccpPopover = document.getElementById("custom-color-picker-popover");

const ccpSvCanvas = document.getElementById("ccp-sv-canvas");

const ccpSvThumb = document.getElementById("ccp-sv-thumb");

const ccpHueCanvas = document.getElementById("ccp-hue-canvas");

const ccpHueThumb = document.getElementById("ccp-hue-thumb");

const ccpCurrentSwatch = document.getElementById("ccp-current-swatch");

const ccpEyedropper = document.getElementById("ccp-eyedropper");

const ccpInputR = document.getElementById("ccp-input-r");

const ccpInputG = document.getElementById("ccp-input-g");

const ccpInputB = document.getElementById("ccp-input-b");

const ccpInputHex = document.getElementById("ccp-input-hex");

let ccpHue = 265;

let ccpSat = .75;

let ccpVal = .08;

let ccpDraggingSv = false;

let ccpDraggingHue = false;

function ccpHsvToRgb(h, s, v) {
  const c = v * s;
  const x = c * (1 - Math.abs(h / 60 % 2 - 1));
  const m = v - c;
  let r = 0, g = 0, b = 0;
  if (h < 60) {
    r = c;
    g = x;
    b = 0;
  } else if (h < 120) {
    r = x;
    g = c;
    b = 0;
  } else if (h < 180) {
    r = 0;
    g = c;
    b = x;
  } else if (h < 240) {
    r = 0;
    g = x;
    b = c;
  } else if (h < 300) {
    r = x;
    g = 0;
    b = c;
  } else {
    r = c;
    g = 0;
    b = x;
  }
  return {
    r: Math.round((r + m) * 255),
    g: Math.round((g + m) * 255),
    b: Math.round((b + m) * 255)
  };
}

function ccpRgbToHsv(r, g, b) {
  r /= 255;
  g /= 255;
  b /= 255;
  const max = Math.max(r, g, b), min = Math.min(r, g, b);
  const d = max - min;
  let h = 0;
  if (d !== 0) {
    if (max === r) h = (g - b) / d % 6; else if (max === g) h = (b - r) / d + 2; else h = (r - g) / d + 4;
    h *= 60;
    if (h < 0) h += 360;
  }
  const s = max === 0 ? 0 : d / max;
  return {
    h: h,
    s: s,
    v: max
  };
}

function ccpRgbToHex(r, g, b) {
  return "#" + [ r, g, b ].map(n => n.toString(16).padStart(2, "0")).join("");
}

function ccpHexToRgb(hex) {
  const m = hex.replace("#", "").match(/^([0-9a-f]{6})$/i);
  if (!m) return null;
  const num = parseInt(m[1], 16);
  return {
    r: num >> 16 & 255,
    g: num >> 8 & 255,
    b: num & 255
  };
}

function ccpDrawSvCanvas() {
  const ctx = ccpSvCanvas.getContext("2d");
  const w = ccpSvCanvas.width, h = ccpSvCanvas.height;
  const hueRgb = ccpHsvToRgb(ccpHue, 1, 1);
  ctx.fillStyle = `rgb(${hueRgb.r},${hueRgb.g},${hueRgb.b})`;
  ctx.fillRect(0, 0, w, h);
  const whiteGrad = ctx.createLinearGradient(0, 0, w, 0);
  whiteGrad.addColorStop(0, "rgba(255,255,255,1)");
  whiteGrad.addColorStop(1, "rgba(255,255,255,0)");
  ctx.fillStyle = whiteGrad;
  ctx.fillRect(0, 0, w, h);
  const blackGrad = ctx.createLinearGradient(0, 0, 0, h);
  blackGrad.addColorStop(0, "rgba(0,0,0,0)");
  blackGrad.addColorStop(1, "rgba(0,0,0,1)");
  ctx.fillStyle = blackGrad;
  ctx.fillRect(0, 0, w, h);
}

function ccpDrawHueCanvas() {
  const ctx = ccpHueCanvas.getContext("2d");
  const w = ccpHueCanvas.width, h = ccpHueCanvas.height;
  const grad = ctx.createLinearGradient(0, 0, w, 0);
  for (let i = 0; i <= 360; i += 30) {
    const rgb = ccpHsvToRgb(i, 1, 1);
    grad.addColorStop(i / 360, `rgb(${rgb.r},${rgb.g},${rgb.b})`);
  }
  ctx.fillStyle = grad;
  ctx.fillRect(0, 0, w, h);
}

function ccpUpdateThumbs() {
  ccpSvThumb.style.left = ccpSat * 100 + "%";
  ccpSvThumb.style.top = (1 - ccpVal) * 100 + "%";
  ccpHueThumb.style.left = ccpHue / 360 * 100 + "%";
}

function ccpUpdateFromHsv(skipInputSync) {
  const rgb = ccpHsvToRgb(ccpHue, ccpSat, ccpVal);
  const hex = ccpRgbToHex(rgb.r, rgb.g, rgb.b);
  ccpCurrentSwatch.style.backgroundColor = hex;
  ccpSwatch.style.backgroundColor = hex;
  ccpUpdateThumbs();
  if (!skipInputSync) {
    ccpInputR.value = rgb.r;
    ccpInputG.value = rgb.g;
    ccpInputB.value = rgb.b;
    ccpInputHex.value = hex;
  }
  if (backgroundColorPicker) backgroundColorPicker.value = hex;
  applyBackgroundColor(hex);
  saveBackgroundColor(hex);
  setActivePresetSwatch(hex);
}

function ccpSetFromRgb(r, g, b) {
  const hsv = ccpRgbToHsv(r, g, b);
  ccpHue = hsv.h;
  ccpSat = hsv.s;
  ccpVal = hsv.v;
  ccpDrawSvCanvas();
  ccpUpdateFromHsv(false);
}

function ccpSetFromHex(hex) {
  const rgb = ccpHexToRgb(hex);
  if (!rgb) return;
  ccpSetFromRgb(rgb.r, rgb.g, rgb.b);
}

function ccpHandleSvPointer(clientX, clientY) {
  const rect = ccpSvCanvas.getBoundingClientRect();
  let x = (clientX - rect.left) / rect.width;
  let y = (clientY - rect.top) / rect.height;
  x = Math.max(0, Math.min(1, x));
  y = Math.max(0, Math.min(1, y));
  ccpSat = x;
  ccpVal = 1 - y;
  ccpUpdateFromHsv(false);
}

function ccpHandleHuePointer(clientX) {
  const rect = ccpHueCanvas.getBoundingClientRect();
  let x = (clientX - rect.left) / rect.width;
  x = Math.max(0, Math.min(1, x));
  ccpHue = x * 360;
  ccpDrawSvCanvas();
  ccpUpdateFromHsv(false);
}

if (ccpSvCanvas) {
  ccpSvCanvas.addEventListener("mousedown", e => {
    ccpDraggingSv = true;
    ccpHandleSvPointer(e.clientX, e.clientY);
  });
}

if (ccpHueCanvas) {
  ccpHueCanvas.addEventListener("mousedown", e => {
    ccpDraggingHue = true;
    ccpHandleHuePointer(e.clientX);
  });
}

document.addEventListener("mousemove", e => {
  if (ccpDraggingSv) ccpHandleSvPointer(e.clientX, e.clientY);
  if (ccpDraggingHue) ccpHandleHuePointer(e.clientX);
});

document.addEventListener("mouseup", () => {
  ccpDraggingSv = false;
  ccpDraggingHue = false;
});

if (ccpSvCanvas) {
  ccpSvCanvas.addEventListener("touchstart", e => {
    ccpDraggingSv = true;
    const t = e.touches[0];
    ccpHandleSvPointer(t.clientX, t.clientY);
  }, {
    passive: true
  });
}

if (ccpHueCanvas) {
  ccpHueCanvas.addEventListener("touchstart", e => {
    ccpDraggingHue = true;
    const t = e.touches[0];
    ccpHandleHuePointer(t.clientX);
  }, {
    passive: true
  });
}

document.addEventListener("touchmove", e => {
  if (!ccpDraggingSv && !ccpDraggingHue) return;
  const t = e.touches[0];
  if (ccpDraggingSv) ccpHandleSvPointer(t.clientX, t.clientY);
  if (ccpDraggingHue) ccpHandleHuePointer(t.clientX);
}, {
  passive: true
});

document.addEventListener("touchend", () => {
  ccpDraggingSv = false;
  ccpDraggingHue = false;
});

function ccpClampChannel(val) {
  const n = parseInt(val, 10);
  if (isNaN(n)) return 0;
  return Math.max(0, Math.min(255, n));
}

if (ccpInputR) {
  ccpInputR.addEventListener("input", () => {
    ccpSetFromRgb(ccpClampChannel(ccpInputR.value), ccpClampChannel(ccpInputG.value), ccpClampChannel(ccpInputB.value));
  });
}

if (ccpInputG) {
  ccpInputG.addEventListener("input", () => {
    ccpSetFromRgb(ccpClampChannel(ccpInputR.value), ccpClampChannel(ccpInputG.value), ccpClampChannel(ccpInputB.value));
  });
}

if (ccpInputB) {
  ccpInputB.addEventListener("input", () => {
    ccpSetFromRgb(ccpClampChannel(ccpInputR.value), ccpClampChannel(ccpInputG.value), ccpClampChannel(ccpInputB.value));
  });
}

if (ccpInputHex) {
  ccpInputHex.addEventListener("input", () => {
    let val = ccpInputHex.value.trim();
    if (!val.startsWith("#")) val = "#" + val;
    if (/^#[0-9a-fA-F]{6}$/.test(val)) ccpSetFromHex(val);
  });
}

if (ccpEyedropper) {
  ccpEyedropper.addEventListener("click", async () => {
    if (!window.EyeDropper) return;
    try {
      const result = await (new window.EyeDropper).open();
      ccpSetFromHex(result.sRGBHex);
    } catch (err) {}
  });
  if (!window.EyeDropper) ccpEyedropper.style.display = "none";
}

function ccpOpenPopover() {
  ccpRoot.classList.add("open");
  ccpSwatch.setAttribute("aria-expanded", "true");
}

function ccpClosePopover() {
  ccpRoot.classList.remove("open");
  ccpSwatch.setAttribute("aria-expanded", "false");
}

if (ccpSwatch) {
  ccpSwatch.addEventListener("click", e => {
    e.stopPropagation();
    if (ccpRoot.classList.contains("open")) ccpClosePopover(); else ccpOpenPopover();
  });
}

document.addEventListener("click", e => {
  if (!ccpRoot) return;
  if (!ccpRoot.contains(e.target)) ccpClosePopover();
});

document.addEventListener("keydown", e => {
  if (e.key === "Escape") ccpClosePopover();
});

if (ccpSvCanvas && ccpHueCanvas) {
  ccpDrawSvCanvas();
  ccpDrawHueCanvas();
}

const backgroundColorPicker = document.getElementById("background-color-picker");

const backgroundColorPresets = document.getElementById("background-color-presets");

const backgroundColorResetBtn = document.getElementById("background-color-reset");

const backgroundColorPresetDropdown = document.getElementById("background-color-preset-dropdown");

const backgroundColorPresetToggle = document.getElementById("background-color-preset-toggle");

const backgroundColorPresetToggleSwatch = document.getElementById("background-color-preset-toggle-swatch");

const backgroundColorPresetActiveName = document.getElementById("background-color-preset-active-name");

function applyBackgroundColor(color) {
  const isPresetTheme = !color || color === "default" || color === "rgb";
  body.classList.toggle("bg-rgb", color === "rgb");
  if (isPresetTheme) {
    body.style.removeProperty("background-color");
    body.style.removeProperty("background-image");
  } else {
    body.style.backgroundColor = color;
    body.style.backgroundImage = "none";
  }
  syncPipBodies();
}

function saveBackgroundColor(color) {
  if (!color || color === "default") {
    localStorage.removeItem(BACKGROUND_COLOR_STORAGE_KEY);
  } else {
    localStorage.setItem(BACKGROUND_COLOR_STORAGE_KEY, color);
  }
}

function setActivePresetSwatch(color) {
  if (!backgroundColorPresets) return;
  const swatches = backgroundColorPresets.querySelectorAll(".color-preset-swatch");
  let matched = null;
  swatches.forEach(sw => {
    const isMatch = sw.dataset.color === color;
    sw.classList.toggle("active", isMatch);
    if (isMatch) matched = sw;
  });
  if (backgroundColorPresetToggleSwatch) {
    backgroundColorPresetToggleSwatch.style.background = matched ? matched.style.background || matched.style.backgroundColor : "linear-gradient(135deg,#000000,#00d2ff)";
  }
  if (backgroundColorPresetActiveName) {
    backgroundColorPresetActiveName.textContent = matched ? matched.dataset.name : "Custom";
  }
  if (ccpSwatch && color && color !== "default" && color !== "rgb") {
    ccpSwatch.style.backgroundColor = color;
    if (ccpCurrentSwatch) ccpCurrentSwatch.style.backgroundColor = color;
    if (ccpInputHex) ccpInputHex.value = color;
    const rgb = ccpHexToRgb(color);
    if (rgb) {
      if (ccpInputR) ccpInputR.value = rgb.r;
      if (ccpInputG) ccpInputG.value = rgb.g;
      if (ccpInputB) ccpInputB.value = rgb.b;
      const hsv = ccpRgbToHsv(rgb.r, rgb.g, rgb.b);
      ccpHue = hsv.h;
      ccpSat = hsv.s;
      ccpVal = hsv.v;
      if (ccpSvCanvas) ccpDrawSvCanvas();
      ccpUpdateThumbs();
    }
  }
}

function closeColorPresetDropdown() {
  if (!backgroundColorPresetDropdown) return;
  backgroundColorPresetDropdown.classList.remove("open");
  if (backgroundColorPresetToggle) backgroundColorPresetToggle.setAttribute("aria-expanded", "false");
}

function toggleColorPresetDropdown() {
  if (!backgroundColorPresetDropdown) return;
  const isOpen = backgroundColorPresetDropdown.classList.toggle("open");
  if (backgroundColorPresetToggle) backgroundColorPresetToggle.setAttribute("aria-expanded", String(isOpen));
}

function loadSavedBackgroundColor() {
  const saved = localStorage.getItem(BACKGROUND_COLOR_STORAGE_KEY) || localStorage.getItem(LEGACY_BACKGROUND_COLOR_STORAGE_KEY);
  if (saved) {
    applyBackgroundColor(saved);
    if (backgroundColorPicker) backgroundColorPicker.value = saved;
    setActivePresetSwatch(saved);
  } else {
    setActivePresetSwatch("default");
  }
}

if (backgroundColorPicker) {
  backgroundColorPicker.addEventListener("input", () => {
    applyBackgroundColor(backgroundColorPicker.value);
    saveBackgroundColor(backgroundColorPicker.value);
    setActivePresetSwatch(backgroundColorPicker.value);
  });
}

if (backgroundColorPresetToggle) {
  backgroundColorPresetToggle.addEventListener("click", e => {
    e.stopPropagation();
    toggleColorPresetDropdown();
  });
}

if (backgroundColorPresets) {
  backgroundColorPresets.addEventListener("click", e => {
    const swatch = e.target.closest(".color-preset-swatch");
    if (!swatch) return;
    const color = swatch.dataset.color;
    applyBackgroundColor(color);
    saveBackgroundColor(color);
    if (backgroundColorPicker && color !== "default" && color !== "rgb") backgroundColorPicker.value = color;
    setActivePresetSwatch(color);
    closeColorPresetDropdown();
  });
}

if (backgroundColorResetBtn) {
  backgroundColorResetBtn.addEventListener("click", () => {
    applyBackgroundColor("default");
    saveBackgroundColor("default");
    if (backgroundColorPicker) backgroundColorPicker.value = "#000000";
    setActivePresetSwatch("default");
    closeColorPresetDropdown();
  });
}

document.addEventListener("click", e => {
  if (!backgroundColorPresetDropdown) return;
  if (!backgroundColorPresetDropdown.contains(e.target)) closeColorPresetDropdown();
});

document.addEventListener("keydown", e => {
  if (e.key === "Escape") closeColorPresetDropdown();
});

loadSavedBackgroundColor();

document.getElementById("goto-video").addEventListener("click", () => {
  if (userAccount) userAccount.showVideoPage();
});

document.getElementById("goto-music").addEventListener("click", () => {
  if (userAccount) userAccount.showMusicPage();
});

document.getElementById("goto-podcast-from-music").addEventListener("click", () => {
  if (userAccount) userAccount.showPodcastPage();
});

document.getElementById("goto-music-from-podcast").addEventListener("click", () => {
  if (userAccount) userAccount.showMusicPage();
});

document.getElementById("goto-podcast-from-video").addEventListener("click", () => {
  if (userAccount) userAccount.showPodcastPage();
});

document.getElementById("goto-video-from-podcast").addEventListener("click", () => {
  if (userAccount) userAccount.showVideoPage();
});

document.getElementById("goto-documentary-from-music").addEventListener("click", () => {
  if (userAccount) userAccount.showDocumentaryPage();
});

document.getElementById("goto-movie-from-music").addEventListener("click", () => {
  if (userAccount) userAccount.showMoviePage();
});

document.getElementById("goto-webseries-from-music").addEventListener("click", () => {
  if (userAccount) userAccount.showWebSeriesPage();
});

document.getElementById("goto-games-from-music").addEventListener("click", () => {
  if (userAccount) userAccount.showGamesPage();
});

document.getElementById("goto-books-from-music").addEventListener("click", () => {
  if (userAccount) userAccount.showBooksPage();
});

document.getElementById("goto-documentary-from-podcast").addEventListener("click", () => {
  if (userAccount) userAccount.showDocumentaryPage();
});

document.getElementById("goto-movie-from-podcast").addEventListener("click", () => {
  if (userAccount) userAccount.showMoviePage();
});

document.getElementById("goto-webseries-from-podcast").addEventListener("click", () => {
  if (userAccount) userAccount.showWebSeriesPage();
});

document.getElementById("goto-games-from-podcast").addEventListener("click", () => {
  if (userAccount) userAccount.showGamesPage();
});

document.getElementById("goto-books-from-podcast").addEventListener("click", () => {
  if (userAccount) userAccount.showBooksPage();
});

document.getElementById("goto-documentary-from-video").addEventListener("click", () => {
  if (userAccount) userAccount.showDocumentaryPage();
});

document.getElementById("goto-movie-from-video").addEventListener("click", () => {
  if (userAccount) userAccount.showMoviePage();
});

document.getElementById("goto-webseries-from-video").addEventListener("click", () => {
  if (userAccount) userAccount.showWebSeriesPage();
});

document.getElementById("goto-games-from-video").addEventListener("click", () => {
  if (userAccount) userAccount.showGamesPage();
});

document.getElementById("goto-books-from-video").addEventListener("click", () => {
  if (userAccount) userAccount.showBooksPage();
});

document.getElementById("goto-music-from-documentary").addEventListener("click", () => {
  if (userAccount) userAccount.showMusicPage();
});

document.getElementById("goto-podcast-from-documentary").addEventListener("click", () => {
  if (userAccount) userAccount.showPodcastPage();
});

document.getElementById("goto-video-from-documentary").addEventListener("click", () => {
  if (userAccount) userAccount.showVideoPage();
});

document.getElementById("goto-movie-from-documentary").addEventListener("click", () => {
  if (userAccount) userAccount.showMoviePage();
});

document.getElementById("goto-webseries-from-documentary").addEventListener("click", () => {
  if (userAccount) userAccount.showWebSeriesPage();
});

document.getElementById("goto-games-from-documentary").addEventListener("click", () => {
  if (userAccount) userAccount.showGamesPage();
});

document.getElementById("goto-books-from-documentary").addEventListener("click", () => {
  if (userAccount) userAccount.showBooksPage();
});

document.getElementById("goto-music-from-movie").addEventListener("click", () => {
  if (userAccount) userAccount.showMusicPage();
});

document.getElementById("goto-podcast-from-movie").addEventListener("click", () => {
  if (userAccount) userAccount.showPodcastPage();
});

document.getElementById("goto-video-from-movie").addEventListener("click", () => {
  if (userAccount) userAccount.showVideoPage();
});

document.getElementById("goto-documentary-from-movie").addEventListener("click", () => {
  if (userAccount) userAccount.showDocumentaryPage();
});

document.getElementById("goto-webseries-from-movie").addEventListener("click", () => {
  if (userAccount) userAccount.showWebSeriesPage();
});

document.getElementById("goto-games-from-movie").addEventListener("click", () => {
  if (userAccount) userAccount.showGamesPage();
});

document.getElementById("goto-books-from-movie").addEventListener("click", () => {
  if (userAccount) userAccount.showBooksPage();
});

document.getElementById("goto-music-from-webseries").addEventListener("click", () => {
  if (userAccount) userAccount.showMusicPage();
});

document.getElementById("goto-podcast-from-webseries").addEventListener("click", () => {
  if (userAccount) userAccount.showPodcastPage();
});

document.getElementById("goto-video-from-webseries").addEventListener("click", () => {
  if (userAccount) userAccount.showVideoPage();
});

document.getElementById("goto-documentary-from-webseries").addEventListener("click", () => {
  if (userAccount) userAccount.showDocumentaryPage();
});

document.getElementById("goto-movie-from-webseries").addEventListener("click", () => {
  if (userAccount) userAccount.showMoviePage();
});

document.getElementById("goto-games-from-webseries").addEventListener("click", () => {
  if (userAccount) userAccount.showGamesPage();
});

document.getElementById("goto-books-from-webseries").addEventListener("click", () => {
  if (userAccount) userAccount.showBooksPage();
});

document.getElementById("goto-music-from-games").addEventListener("click", () => {
  if (userAccount) userAccount.showMusicPage();
});

document.getElementById("goto-podcast-from-games").addEventListener("click", () => {
  if (userAccount) userAccount.showPodcastPage();
});

document.getElementById("goto-video-from-games").addEventListener("click", () => {
  if (userAccount) userAccount.showVideoPage();
});

document.getElementById("goto-documentary-from-games").addEventListener("click", () => {
  if (userAccount) userAccount.showDocumentaryPage();
});

document.getElementById("goto-movie-from-games").addEventListener("click", () => {
  if (userAccount) userAccount.showMoviePage();
});

document.getElementById("goto-webseries-from-games").addEventListener("click", () => {
  if (userAccount) userAccount.showWebSeriesPage();
});

document.getElementById("goto-books-from-games").addEventListener("click", () => {
  if (userAccount) userAccount.showBooksPage();
});

document.getElementById("goto-music-from-books").addEventListener("click", () => {
  if (userAccount) userAccount.showMusicPage();
});

document.getElementById("goto-podcast-from-books").addEventListener("click", () => {
  if (userAccount) userAccount.showPodcastPage();
});

document.getElementById("goto-video-from-books").addEventListener("click", () => {
  if (userAccount) userAccount.showVideoPage();
});

document.getElementById("goto-documentary-from-books").addEventListener("click", () => {
  if (userAccount) userAccount.showDocumentaryPage();
});

document.getElementById("goto-movie-from-books").addEventListener("click", () => {
  if (userAccount) userAccount.showMoviePage();
});

document.getElementById("goto-webseries-from-books").addEventListener("click", () => {
  if (userAccount) userAccount.showWebSeriesPage();
});

document.getElementById("goto-games-from-books").addEventListener("click", () => {
  if (userAccount) userAccount.showGamesPage();
});

function volumeIconFor(value, muted) {
  if (muted || value === 0) return "🔇";
  if (value < 50) return "🔈";
  if (value < 80) return "🔉";
  return "🔊";
}

function setupVolumeControl(mediaEl, rangeEl, muteBtn, labelEl, storageKey) {
  const saved = appGet(storageKey, null);
  const initial = saved !== null ? Math.round(Number(saved) * 100) : 100;
  rangeEl.value = String(Math.min(100, Math.max(0, initial)));
  let lastNonZero = Number(rangeEl.value) || 100;
  function apply() {
    const v = Number(rangeEl.value);
    mediaEl.volume = v / 100;
    mediaEl.muted = v === 0;
    appSet(storageKey, v / 100);
    labelEl.textContent = `${v}%`;
    muteBtn.textContent = volumeIconFor(v, mediaEl.muted);
    updateRangeFill(rangeEl);
  }
  rangeEl.addEventListener("input", () => {
    if (Number(rangeEl.value) > 0) lastNonZero = Number(rangeEl.value);
    apply();
  });
  muteBtn.addEventListener("click", () => {
    if (Number(rangeEl.value) > 0) {
      lastNonZero = Number(rangeEl.value);
      rangeEl.value = "0";
    } else {
      rangeEl.value = String(lastNonZero || 100);
    }
    apply();
  });
  apply();
}

function refreshVolumeControlFromStorage(rangeEl, storageKey, apply) {
  const saved = appGet(storageKey, null);
  const initial = saved !== null ? Math.round(Number(saved) * 100) : 100;
  rangeEl.value = String(Math.min(100, Math.max(0, initial)));
  apply();
}

function setupSpeedControl(mediaEl, groupEl, storageKey) {
  const saved = appGet(storageKey, null);
  const rate = saved !== null ? Number(saved) : 1;
  mediaEl.playbackRate = rate;
  const chips = Array.from(groupEl.querySelectorAll(".speed-chip"));
  chips.forEach(chip => {
    chip.classList.toggle("active", Number(chip.dataset.speed) === rate);
    chip.addEventListener("click", () => {
      const speed = Number(chip.dataset.speed);
      mediaEl.playbackRate = speed;
      appSet(storageKey, speed);
      chips.forEach(c => c.classList.remove("active"));
      chip.classList.add("active");
    });
  });
}

let music = [];

let playlists = {};

let currentPlaylist = null;

let currentMusicId = null;

let musicRepeat = false;

let musicLoopPlaylist = false;

let playlistPlaying = false;

let musicPositions = {};

let musicDB;

let musicRecent = [];

const POSITION_SAVE_INTERVAL = 5e3;

let lastMusicPositionSave = 0;

const musicUpload = document.getElementById("music-upload");

const musicList = document.getElementById("music-list");

const musicCount = document.getElementById("music-count");

const musicSearch = document.getElementById("music-search");

const playlistName = document.getElementById("playlist-name");

const playlistsEl = document.getElementById("playlists");

const playlistTitle = document.getElementById("playlist-title");

const musicPlaylistHeaderEl = document.getElementById("music-playlist-header");

const musicPlaylistToolbarEl = document.getElementById("music-playlist-toolbar");

const playlistMusic = document.getElementById("playlist-music");

const audioPlayer = document.getElementById("audio-player");

const currentMusicDisplay = document.getElementById("current-music");

const playPauseBtn = document.getElementById("play-pause");

const nextBtn = document.getElementById("next-music");

const prevBtn = document.getElementById("prev-music");

const repeatBtn = document.getElementById("toggle-repeat");

const musicProgress = document.getElementById("music-progress");

const currentTimeEl = document.getElementById("current-time");

const durationEl = document.getElementById("duration");

const selectAllMusicCheckbox = document.getElementById("select-all-music");

const deleteSelectedMusicBtn = document.getElementById("btn-delete-selected");

const musicVolume = document.getElementById("music-volume");

const musicMuteBtn = document.getElementById("music-mute-btn");

const musicVolumeLabel = document.getElementById("music-volume-label");

const musicSpeedGroup = document.getElementById("music-speed-group");

const exportPlaylistBtn = document.getElementById("btn-export-playlist");

const playlistImportInput = document.getElementById("playlist-import");

const musicRecentList = document.getElementById("music-recent-list");

const clearMusicRecentBtn = document.getElementById("btn-clear-music-recent");

function ensureUserIdIndex(store) {
  if (!store.indexNames.contains("userId")) {
    store.createIndex("userId", "userId");
  }
}

function openTerminalDB(dbName, storeConfigs) {
  return openIndexedDBSafely(dbName, 2, e => {
    const db = e.target.result;
    const tx = e.target.transaction;
    storeConfigs.forEach(cfg => {
      let store;
      if (!db.objectStoreNames.contains(cfg.name)) {
        store = db.createObjectStore(cfg.name, cfg.options || {
          keyPath: "id",
          autoIncrement: true
        });
      } else {
        store = tx.objectStore(cfg.name);
      }
      if (cfg.userIdIndex !== false) ensureUserIdIndex(store);
    });
  });
}

function loadUserRecordsIndexed(db, storeName, userId) {
  return new Promise((resolve, reject) => {
    if (!db || !userId) return resolve([]);
    const out = [];
    const tx = db.transaction(storeName, "readonly");
    const store = tx.objectStore(storeName);
    const hasIndex = store.indexNames.contains("userId");
    const source = hasIndex ? store.index("userId") : store;
    const range = hasIndex ? IDBKeyRange.only(userId) : undefined;
    const cursorReq = source.openCursor(range);
    cursorReq.onsuccess = e => {
      const cursor = e.target.result;
      if (cursor) {
        if (hasIndex || cursor.value.userId === userId) out.push(cursor.value);
        cursor.continue();
      } else {
        resolve(out);
      }
    };
    cursorReq.onerror = () => reject(cursorReq.error);
    tx.onerror = () => reject(tx.error);
  });
}

const VIRTUALIZE_THRESHOLD = 500;

const ROW_WINDOW_SIZE = 60;

function renderListBatched(container, items, buildRowFn) {
  if (!container) return;
  if (items.length <= VIRTUALIZE_THRESHOLD) {
    if (container._virtualScrollHandler) {
      container.removeEventListener("scroll", container._virtualScrollHandler);
      container._virtualScrollHandler = null;
    }
    container.classList.remove("virtualized-list");
    container.innerHTML = "";
    const frag = document.createDocumentFragment();
    for (let i = 0; i < items.length; i++) frag.appendChild(buildRowFn(items[i], i));
    container.appendChild(frag);
    return;
  }
  container.classList.add("virtualized-list");
  const rowHeight = parseInt(container.dataset.rowHeight || "37", 10);
  const paintWindow = () => {
    const scrollTop = container.scrollTop;
    const viewportRows = Math.ceil((container.clientHeight || 600) / rowHeight);
    const windowSize = Math.max(ROW_WINDOW_SIZE, viewportRows + 20);
    let start = Math.max(0, Math.floor(scrollTop / rowHeight) - Math.floor(windowSize / 4));
    start = Math.min(start, Math.max(0, items.length - windowSize));
    const end = Math.min(items.length, start + windowSize);
    container.innerHTML = "";
    const topSpacer = document.createElement("li");
    topSpacer.className = "virtual-spacer virtual-spacer-top";
    topSpacer.style.height = `${start * rowHeight}px`;
    const bottomSpacer = document.createElement("li");
    bottomSpacer.className = "virtual-spacer virtual-spacer-bottom";
    bottomSpacer.style.height = `${(items.length - end) * rowHeight}px`;
    const frag = document.createDocumentFragment();
    frag.appendChild(topSpacer);
    for (let i = start; i < end; i++) frag.appendChild(buildRowFn(items[i], i));
    frag.appendChild(bottomSpacer);
    container.appendChild(frag);
  };
  if (container._virtualScrollHandler) {
    container.removeEventListener("scroll", container._virtualScrollHandler);
  }
  let ticking = false;
  container._virtualScrollHandler = () => {
    if (ticking) return;
    ticking = true;
    window.requestAnimationFrame(() => {
      paintWindow();
      ticking = false;
    });
  };
  container.addEventListener("scroll", container._virtualScrollHandler);
  paintWindow();
}

function openMusicDB() {
  return openTerminalDB("MusicPlayerDB", [ {
    name: "music"
  } ]);
}

async function loadMusicFromDB() {
  if (!musicDB || !currentUserId) {
    music.length = 0;
    renderMusic(musicSearch.value);
    return;
  }
  const rows = await loadUserRecordsIndexed(musicDB, "music", currentUserId);
  music.length = 0;
  music.push(...rows);
  restoreListSortMode("music", music);
  renderMusic(musicSearch.value);
  if (userAccount) userAccount.updateAccountInfo();
}

function renderMusic(filter = "") {
  const f = filter.toLowerCase();
  const visible = music.filter(song => !f || song.name.toLowerCase().includes(f));
  renderListBatched(musicList, visible, song => {
    const li = document.createElement("li");
    if (song.id === currentMusicId) li.classList.add("selected");
    const cb = document.createElement("input");
    cb.type = "checkbox";
    cb.dataset.id = song.id;
    cb.addEventListener("change", () => {
      li.classList.toggle("selected", cb.checked);
      const allChecked = Array.from(document.querySelectorAll("#music-list input[type=checkbox]")).every(c => c.checked);
      selectAllMusicCheckbox.checked = allChecked;
    });
    const name = document.createElement("span");
    const count = getPlayCount("music", song.name);
    name.textContent = count > 0 ? `${song.name}  ·  ${count} play${count === 1 ? "" : "s"}` : song.name;
    const playBtn = document.createElement("button");
    playBtn.textContent = "▶";
    playBtn.className = "media-row-play-btn";
    playBtn.addEventListener("click", () => {
      playlistPlaying = false;
      currentPlaylist = null;
      playMusicById(song.id);
    });
    li.append(cb, name, playBtn);
    attachMusicDragSource(li, song);
    attachRowClickToggle(li, cb, playBtn);
    return li;
  });
  musicCount.textContent = `${music.length}`;
}

function attachMusicDragSource(li, song) {
  li.draggable = true;
  li.addEventListener("dragstart", e => {
    e.dataTransfer.setData("text/plain", String(song.id));
    e.dataTransfer.effectAllowed = "copy";
    li.classList.add("dragging");
  });
  li.addEventListener("dragend", () => li.classList.remove("dragging"));
}

function playMusicById(id, isResume) {
  const song = music.find(s => s.id === id);
  if (!song) return;
  let url;
  try {
    url = URL.createObjectURL(song.blob);
  } catch (err) {
    console.error("Failed to create a playback URL for this song", err);
    alert("Could not load this song for playback.");
    return;
  }
  currentMusicId = id;
  if (audioPlayer.dataset.url) URL.revokeObjectURL(audioPlayer.dataset.url);
  audioPlayer.src = url;
  audioPlayer.dataset.url = url;
  const resumeAt = musicPositions[id];
  if (resumeAt) {
    const restorePosition = () => {
      if (resumeAt < audioPlayer.duration - 2) audioPlayer.currentTime = resumeAt;
      audioPlayer.removeEventListener("loadedmetadata", restorePosition);
    };
    audioPlayer.addEventListener("loadedmetadata", restorePosition);
  }
  currentMusicDisplay.textContent = song.name;
  appSet("lastMusicId", id);
  if (isResume) {
    playPauseBtn.textContent = "Play";
  } else {
    audioPlayer.play().then(() => {
      playPauseBtn.textContent = "Pause";
    }).catch(err => {
      console.error("Playback failed to start", err);
      playPauseBtn.textContent = "Play";
    });
  }
  if (!isResume) recordPlay("music", song.name, currentMusicSource());
  renderMusic(musicSearch.value);
  renderPlaylistMusic();
}

function currentMusicSource() {
  return playlistPlaying && currentPlaylist ? `Playlist: ${isSmartPlaylist(currentPlaylist) ? smartPlaylistLabel(currentPlaylist) : currentPlaylist}` : "Library";
}

function playNextMusic() {
  const queuedId = consumeQueueNext("music");
  if (queuedId !== null) return playMusicById(queuedId);
  if (playlistPlaying && currentPlaylist) {
    const ctx = musicPlaylistCtx();
    const list = getActivePlaylistIds(ctx);
    const shuffle = !isSmartPlaylist(currentPlaylist) && getPlaylistMeta(musicPlaylistMeta, currentPlaylist).shuffle;
    const next = pickNextInList(list, currentMusicId, shuffle);
    if (next !== null) return playMusicById(next);
    if (musicLoopPlaylist && list.length) return playMusicById(shuffle ? list[Math.floor(Math.random() * list.length)] : list[0]);
    playlistPlaying = false;
    return;
  }
  if (!music.length) return;
  const idx = music.findIndex(s => s.id === currentMusicId);
  const nextIdx = idx === -1 ? 0 : (idx + 1) % music.length;
  playMusicById(music[nextIdx].id);
}

function playPrevMusic() {
  if (playlistPlaying && currentPlaylist) {
    const list = getActivePlaylistIds(musicPlaylistCtx());
    const idx = list.indexOf(currentMusicId);
    if (idx > 0) return playMusicById(list[idx - 1]);
    return;
  }
  if (!music.length) return;
  const idx = music.findIndex(s => s.id === currentMusicId);
  const prevIdx = idx <= 0 ? music.length - 1 : idx - 1;
  playMusicById(music[prevIdx].id);
}

function saveMusicRecent() {
  appSet("musicRecent", musicRecent);
}

function renderMusicRecent() {
  if (!musicRecentList) return;
  musicRecentList.innerHTML = "";
  const sorted = [ ...musicRecent ].sort((a, b) => b.addedAt - a.addedAt);
  if (!sorted.length) {
    musicRecentList.appendChild(buildHistoryRow({
      empty: true,
      title: "No recent uploads in Music Terminal.",
      removeClass: "recent-remove-btn"
    }));
    return;
  }
  sorted.forEach(entry => {
    musicRecentList.appendChild(buildHistoryRow({
      mediaType: "music",
      title: entry.name,
      metaParts: [ {
        className: "history-timestamp",
        text: new Date(entry.addedAt).toLocaleString()
      } ],
      removeClass: "recent-remove-btn",
      onRemove: () => {
        musicRecent = musicRecent.filter(e => e.entryId !== entry.entryId);
        saveMusicRecent();
        renderMusicRecent();
      }
    }));
  });
}

if (clearMusicRecentBtn) {
  clearMusicRecentBtn.addEventListener("click", () => {
    musicRecent = [];
    saveMusicRecent();
    renderMusicRecent();
  });
}

musicUpload.addEventListener("change", async e => {
  if (!musicDB || !currentUserId) return;
  const rawFiles = [ ...e.target.files ];
  if (!rawFiles.length) return;
  const files = filterUploadedMediaFiles(rawFiles, "audio");
  if (!files.length) {
    musicUpload.value = "";
    return;
  }
  const existingKeys = new Set(music.map(s => `${s.name.toLowerCase()}|${s.blob.size}`));
  const newFiles = files.filter(f => !existingKeys.has(`${f.name.toLowerCase()}|${f.size}`));
  const skippedCount = files.length - newFiles.length;
  if (!newFiles.length) {
    musicUpload.value = "";
    if (skippedCount) alert(`Skipped ${skippedCount} duplicate song(s) already in your library.`);
    return;
  }
  const tx = musicDB.transaction("music", "readwrite");
  const store = tx.objectStore("music");
  const addedEntries = [];
  newFiles.forEach(file => {
    const req = store.add({
      name: file.name,
      blob: file,
      userId: currentUserId
    });
    req.onsuccess = () => {
      addedEntries.push({
        entryId: `m${req.result}_${Date.now()}_${Math.random().toString(36).slice(2)}`,
        id: req.result,
        name: file.name,
        addedAt: Date.now()
      });
    };
  });
  tx.oncomplete = () => {
    musicUpload.value = "";
    musicRecent = musicRecent.concat(addedEntries);
    saveMusicRecent();
    renderMusicRecent();
    loadMusicFromDB();
    if (skippedCount) alert(`Added ${newFiles.length} song(s). Skipped ${skippedCount} duplicate(s).`);
  };
  tx.onerror = () => {
    console.error("Failed to save uploaded song(s)", tx.error);
    alert("Could not save the uploaded song file(s).");
  };
});

selectAllMusicCheckbox.addEventListener("change", () => {
  const checked = selectAllMusicCheckbox.checked;
  musicList.querySelectorAll("li").forEach(li => {
    const cb = li.querySelector("input[type=checkbox]");
    if (!cb) return;
    cb.checked = checked;
    li.classList.toggle("selected", checked);
  });
});

musicSearch.addEventListener("input", debounce(() => renderMusic(musicSearch.value)));

document.getElementById("btn-shuffle-music").addEventListener("click", () => {
  shuffleArray(music);
  saveListSortMode("music", "shuffle", music);
  renderMusic(musicSearch.value);
});

document.getElementById("btn-sort-az-music").addEventListener("click", () => {
  music.sort((a, b) => a.name.localeCompare(b.name));
  saveListSortMode("music", "az", music);
  renderMusic(musicSearch.value);
});

document.getElementById("btn-sort-za-music").addEventListener("click", () => {
  music.sort((a, b) => b.name.localeCompare(a.name));
  saveListSortMode("music", "za", music);
  renderMusic(musicSearch.value);
});

if (deleteSelectedMusicBtn) {
  deleteSelectedMusicBtn.addEventListener("click", () => {
    if (!musicDB) return alert("Database not ready");
    const selected = document.querySelectorAll("#music-list input[type=checkbox]:checked");
    if (selected.length === 0) return alert("No songs selected");
    const idsToRemove = Array.from(selected).map(cb => Number(cb.dataset.id)).filter(id => !isNaN(id));
    const tx = musicDB.transaction("music", "readwrite");
    const store = tx.objectStore("music");
    idsToRemove.forEach(id => store.delete(id));
    tx.oncomplete = () => {
      Object.keys(playlists).forEach(name => {
        playlists[name] = playlists[name].filter(id => !idsToRemove.includes(id));
      });
      saveMusicPlaylists();
      idsToRemove.forEach(id => delete musicPositions[id]);
      appSet("musicPositions", musicPositions);
      musicRecent = musicRecent.filter(e => !idsToRemove.includes(e.id));
      saveMusicRecent();
      renderMusicRecent();
      if (currentMusicId !== null && idsToRemove.includes(currentMusicId)) {
        currentMusicId = null;
        currentMusicDisplay.textContent = "No music selected";
        audioPlayer.pause();
        audioPlayer.removeAttribute("src");
        playPauseBtn.textContent = "Play";
      }
      loadMusicFromDB();
      renderPlaylistMusic();
      renderPlaylists();
      if (userAccount) userAccount.updateAccountInfo();
    };
    tx.onerror = () => {
      console.error("Failed to delete selected songs", tx.error);
      alert("Could not delete the selected songs.");
    };
  });
}

playPauseBtn.addEventListener("click", () => {
  if (!currentMusicId && music.length) return playMusicById(music[0].id);
  if (audioPlayer.paused) {
    audioPlayer.play();
    playPauseBtn.textContent = "Pause";
  } else {
    audioPlayer.pause();
    playPauseBtn.textContent = "Play";
  }
});

nextBtn.addEventListener("click", () => {
  playlistPlaying = playlistPlaying && !!currentPlaylist;
  playNextMusic();
});

prevBtn.addEventListener("click", () => playPrevMusic());

repeatBtn.addEventListener("click", () => {
  musicRepeat = !musicRepeat;
  audioPlayer.loop = musicRepeat;
  repeatBtn.textContent = `Repeat: ${musicRepeat ? "On" : "Off"}`;
});

audioPlayer.addEventListener("timeupdate", () => {
  if (!audioPlayer.duration) return;
  musicProgress.value = audioPlayer.currentTime / audioPlayer.duration * 100;
  updateRangeFill(musicProgress);
  currentTimeEl.textContent = formatTime(audioPlayer.currentTime);
  durationEl.textContent = formatTime(audioPlayer.duration);
  if (currentMusicId !== null) {
    const now = Date.now();
    if (now - lastMusicPositionSave > POSITION_SAVE_INTERVAL) {
      lastMusicPositionSave = now;
      musicPositions[currentMusicId] = audioPlayer.currentTime;
      appSet("musicPositions", musicPositions);
    }
  }
});

musicProgress.addEventListener("input", () => {
  if (audioPlayer.duration) audioPlayer.currentTime = musicProgress.value / 100 * audioPlayer.duration;
  updateRangeFill(musicProgress);
});

audioPlayer.addEventListener("pause", () => {
  if (currentMusicId !== null && audioPlayer.duration) {
    musicPositions[currentMusicId] = audioPlayer.currentTime;
    appSet("musicPositions", musicPositions);
  }
});

audioPlayer.addEventListener("ended", () => {
  if (currentMusicId !== null) {
    delete musicPositions[currentMusicId];
    appSet("musicPositions", musicPositions);
  }
  playNextMusic();
});

document.getElementById("forward-10").addEventListener("click", () => {
  audioPlayer.currentTime += 10;
});

document.getElementById("rewind-10").addEventListener("click", () => {
  audioPlayer.currentTime = Math.max(0, audioPlayer.currentTime - 10);
});

(function addMusicLoopPlaylistButton() {
  const controls = document.querySelector("#music-page .player-container .controls");
  if (!controls) return;
  const btn = document.createElement("button");
  btn.className = "action-button";
  btn.textContent = "🔁 Loop Playlist: Off";
  controls.insertBefore(btn, controls.firstChild);
  btn.addEventListener("click", () => {
    musicLoopPlaylist = !musicLoopPlaylist;
    btn.textContent = `🔁 Loop Playlist: ${musicLoopPlaylist ? "On" : "Off"}`;
  });
})();

let videos = [];

let videoPlaylists = {};

let currentVideoPlaylist = null;

let currentVideoId = null;

let videoRepeat = false;

let videoLoopPlaylist = false;

let videoPlaylistPlaying = false;

let videoPositions = {};

let videoDB;

let lastVideoPositionSave = 0;

let videoRecent = [];

const videoUpload = document.getElementById("video-upload");

const videoList = document.getElementById("video-list");

const videoCount = document.getElementById("video-count");

const videoSearch = document.getElementById("video-search");

const videoPlayer = document.getElementById("video-player");

const videoDock = document.getElementById("video-dock");

const videoCurrentDisplay = document.getElementById("current-video");

const playPauseVideoBtn = document.getElementById("play-pause-video");

const nextVideoBtn = document.getElementById("next-video");

const prevVideoBtn = document.getElementById("prev-video");

const toggleRepeatVideoBtn = document.getElementById("toggle-repeat-video");

const videoProgress = document.getElementById("video-progress");

const videoCurrentTimeEl = document.getElementById("video-current-time");

const videoDurationEl = document.getElementById("video-duration");

const videoPlaylistName = document.getElementById("video-playlist-name");

const videoPlaylistsEl = document.getElementById("video-playlists");

const playlistVideos = document.getElementById("playlist-videos");

const videoPlaylistTitle = document.getElementById("video-playlist-title");

const videoPlaylistHeaderEl = document.getElementById("video-playlist-header");

const videoPlaylistToolbarEl = document.getElementById("video-playlist-toolbar");

const videoVolume = document.getElementById("video-volume");

const videoMuteBtn = document.getElementById("video-mute-btn");

const videoVolumeLabel = document.getElementById("video-volume-label");

const videoSpeedGroup = document.getElementById("video-speed-group");

const exportVideoPlaylistBtn = document.getElementById("btn-export-video-playlist");

const videoPlaylistImportInput = document.getElementById("video-playlist-import");

const videoRecentList = document.getElementById("video-recent-list");

const clearVideoRecentBtn = document.getElementById("btn-clear-video-recent");

function openVideoDB() {
  return openTerminalDB("VideoPlayerDB", [ {
    name: "videos"
  } ]);
}

async function loadVideosFromDB() {
  if (!videoDB || !currentUserId) {
    videos.length = 0;
    renderVideos(videoSearch.value);
    return;
  }
  const rows = await loadUserRecordsIndexed(videoDB, "videos", currentUserId);
  videos.length = 0;
  videos.push(...rows);
  restoreListSortMode("video", videos);
  renderVideos(videoSearch.value);
  if (userAccount) userAccount.updateAccountInfo();
}

function renderVideos(filter = "") {
  const f = filter.toLowerCase();
  const visible = videos.filter(video => !f || video.name.toLowerCase().includes(f));
  renderListBatched(videoList, visible, video => {
    const li = document.createElement("li");
    if (video.id === currentVideoId) li.classList.add("selected");
    const cb = document.createElement("input");
    cb.type = "checkbox";
    cb.dataset.id = video.id;
    cb.addEventListener("change", () => li.classList.toggle("selected", cb.checked));
    const name = document.createElement("span");
    const count = getPlayCount("video", video.name);
    name.textContent = count > 0 ? `${video.name}  ·  ${count} play${count === 1 ? "" : "s"}` : video.name;
    const playBtn = document.createElement("button");
    playBtn.textContent = "▶";
    playBtn.className = "media-row-play-btn";
    playBtn.addEventListener("click", () => {
      videoPlaylistPlaying = false;
      currentVideoPlaylist = null;
      playVideoById(video.id);
    });
    li.append(cb, name, playBtn);
    attachVideoDragSource(li, video);
    attachRowClickToggle(li, cb, playBtn);
    return li;
  });
  videoCount.textContent = `${videos.length}`;
}

function attachVideoDragSource(li, video) {
  li.draggable = true;
  li.addEventListener("dragstart", e => {
    e.dataTransfer.setData("text/plain", String(video.id));
    e.dataTransfer.effectAllowed = "copy";
    li.classList.add("dragging");
  });
  li.addEventListener("dragend", () => li.classList.remove("dragging"));
}

function playVideoById(id, isResume) {
  const video = videos.find(v => v.id === id);
  if (!video) return;
  let url;
  try {
    url = URL.createObjectURL(video.blob);
  } catch (err) {
    console.error("Failed to create a playback URL for this video", err);
    alert("Could not load this video for playback.");
    return;
  }
  currentVideoId = id;
  if (videoPlayer.dataset.url) URL.revokeObjectURL(videoPlayer.dataset.url);
  videoPlayer.src = url;
  videoPlayer.dataset.url = url;
  const resumeAt = videoPositions[id];
  if (resumeAt) {
    const restorePosition = () => {
      if (resumeAt < videoPlayer.duration - 2) videoPlayer.currentTime = resumeAt;
      videoPlayer.removeEventListener("loadedmetadata", restorePosition);
    };
    videoPlayer.addEventListener("loadedmetadata", restorePosition);
  }
  videoCurrentDisplay.textContent = video.name;
  appSet("lastVideoId", id);
  if (isResume) {
    playPauseVideoBtn.textContent = "Play";
  } else {
    videoPlayer.play().then(() => {
      playPauseVideoBtn.textContent = "Pause";
    }).catch(err => {
      console.error("Playback failed to start", err);
      playPauseVideoBtn.textContent = "Play";
    });
  }
  if (!isResume) recordPlay("video", video.name, currentVideoSource());
  renderVideos(videoSearch.value);
  renderPlaylistVideos();
}

function currentVideoSource() {
  return videoPlaylistPlaying && currentVideoPlaylist ? `Playlist: ${isSmartPlaylist(currentVideoPlaylist) ? smartPlaylistLabel(currentVideoPlaylist) : currentVideoPlaylist}` : "Library";
}

function playNextVideo() {
  const queuedId = consumeQueueNext("video");
  if (queuedId !== null) return playVideoById(queuedId);
  if (videoPlaylistPlaying && currentVideoPlaylist) {
    const list = getActivePlaylistIds(videoPlaylistCtx());
    const shuffle = !isSmartPlaylist(currentVideoPlaylist) && getPlaylistMeta(videoPlaylistMeta, currentVideoPlaylist).shuffle;
    const next = pickNextInList(list, currentVideoId, shuffle);
    if (next !== null) return playVideoById(next);
    if (videoLoopPlaylist && list.length) return playVideoById(shuffle ? list[Math.floor(Math.random() * list.length)] : list[0]);
    videoPlaylistPlaying = false;
    return;
  }
  if (!videos.length) return;
  const idx = videos.findIndex(v => v.id === currentVideoId);
  const nextIdx = idx === -1 ? 0 : (idx + 1) % videos.length;
  playVideoById(videos[nextIdx].id);
}

function playPrevVideo() {
  if (videoPlaylistPlaying && currentVideoPlaylist) {
    const list = getActivePlaylistIds(videoPlaylistCtx());
    const idx = list.indexOf(currentVideoId);
    if (idx > 0) return playVideoById(list[idx - 1]);
    return;
  }
  if (!videos.length) return;
  const idx = videos.findIndex(v => v.id === currentVideoId);
  const prevIdx = idx <= 0 ? videos.length - 1 : idx - 1;
  playVideoById(videos[prevIdx].id);
}

function saveVideoRecent() {
  appSet("videoRecent", videoRecent);
}

function renderVideoRecent() {
  if (!videoRecentList) return;
  videoRecentList.innerHTML = "";
  const sorted = [ ...videoRecent ].sort((a, b) => b.addedAt - a.addedAt);
  if (!sorted.length) {
    videoRecentList.appendChild(buildHistoryRow({
      empty: true,
      title: "No recent uploads in Video Terminal.",
      removeClass: "recent-remove-btn"
    }));
    return;
  }
  sorted.forEach(entry => {
    videoRecentList.appendChild(buildHistoryRow({
      mediaType: "video",
      title: entry.name,
      metaParts: [ {
        className: "history-timestamp",
        text: new Date(entry.addedAt).toLocaleString()
      } ],
      removeClass: "recent-remove-btn",
      onRemove: () => {
        videoRecent = videoRecent.filter(e => e.entryId !== entry.entryId);
        saveVideoRecent();
        renderVideoRecent();
      }
    }));
  });
}

if (clearVideoRecentBtn) {
  clearVideoRecentBtn.addEventListener("click", () => {
    videoRecent = [];
    saveVideoRecent();
    renderVideoRecent();
  });
}

videoUpload.addEventListener("change", async e => {
  if (!videoDB || !currentUserId) return;
  const rawFiles = [ ...e.target.files ];
  if (!rawFiles.length) return;
  const files = filterUploadedMediaFiles(rawFiles, "video");
  if (!files.length) {
    videoUpload.value = "";
    return;
  }
  const existingKeys = new Set(videos.map(v => `${v.name.toLowerCase()}|${v.blob.size}`));
  const newFiles = files.filter(f => !existingKeys.has(`${f.name.toLowerCase()}|${f.size}`));
  const skippedCount = files.length - newFiles.length;
  if (!newFiles.length) {
    videoUpload.value = "";
    if (skippedCount) alert(`Skipped ${skippedCount} duplicate video(s) already in your library.`);
    return;
  }
  const tx = videoDB.transaction("videos", "readwrite");
  const store = tx.objectStore("videos");
  const addedEntries = [];
  newFiles.forEach(file => {
    const req = store.add({
      name: file.name,
      blob: file,
      userId: currentUserId
    });
    req.onsuccess = () => {
      addedEntries.push({
        entryId: `v${req.result}_${Date.now()}_${Math.random().toString(36).slice(2)}`,
        id: req.result,
        name: file.name,
        addedAt: Date.now()
      });
    };
  });
  tx.oncomplete = () => {
    videoUpload.value = "";
    videoRecent = videoRecent.concat(addedEntries);
    saveVideoRecent();
    renderVideoRecent();
    loadVideosFromDB();
    if (skippedCount) alert(`Added ${newFiles.length} video(s). Skipped ${skippedCount} duplicate(s).`);
  };
  tx.onerror = () => {
    console.error("Failed to save uploaded video(s)", tx.error);
    alert("Could not save the uploaded video file(s).");
  };
});

videoSearch.addEventListener("input", debounce(() => renderVideos(videoSearch.value)));

document.getElementById("btn-shuffle-videos").addEventListener("click", () => {
  shuffleArray(videos);
  saveListSortMode("video", "shuffle", videos);
  renderVideos(videoSearch.value);
});

document.getElementById("btn-sort-az-videos").addEventListener("click", () => {
  videos.sort((a, b) => a.name.localeCompare(b.name));
  saveListSortMode("video", "az", videos);
  renderVideos(videoSearch.value);
});

document.getElementById("btn-sort-za-videos").addEventListener("click", () => {
  videos.sort((a, b) => b.name.localeCompare(a.name));
  saveListSortMode("video", "za", videos);
  renderVideos(videoSearch.value);
});

(function buildVideoSelectAllBar() {
  const container = document.querySelector("#video-page .player-container");
  if (container.querySelector(".video-control-wrapper")) return;
  const wrapper = document.createElement("div");
  wrapper.className = "video-control-wrapper";
  const selectAllLabel = document.createElement("label");
  selectAllLabel.className = "select-all-label";
  const selectAllCheckbox = document.createElement("input");
  selectAllCheckbox.type = "checkbox";
  selectAllLabel.append(selectAllCheckbox, document.createTextNode("Select All Videos"));
  const deleteBtn = document.createElement("button");
  deleteBtn.textContent = "Delete Selected";
  deleteBtn.className = "delete-button";
  wrapper.append(selectAllLabel, deleteBtn);
  container.prepend(wrapper);
  selectAllCheckbox.addEventListener("change", () => {
    document.querySelectorAll("#video-list input[type=checkbox]").forEach(cb => {
      cb.checked = selectAllCheckbox.checked;
      cb.parentElement.classList.toggle("selected", cb.checked);
    });
  });
  videoList.addEventListener("change", e => {
    if (e.target.type !== "checkbox") return;
    const allChecked = Array.from(document.querySelectorAll("#video-list input[type=checkbox]")).every(cb => cb.checked);
    selectAllCheckbox.checked = allChecked;
  });
  deleteBtn.addEventListener("click", () => {
    if (!videoDB) return alert("Database not ready");
    const selected = document.querySelectorAll("#video-list input[type=checkbox]:checked");
    if (!selected.length) return alert("No videos selected");
    const idsToRemove = Array.from(selected).map(cb => Number(cb.dataset.id)).filter(id => !isNaN(id));
    const tx = videoDB.transaction("videos", "readwrite");
    const store = tx.objectStore("videos");
    idsToRemove.forEach(id => store.delete(id));
    tx.oncomplete = () => {
      Object.keys(videoPlaylists).forEach(name => {
        videoPlaylists[name] = videoPlaylists[name].filter(id => !idsToRemove.includes(id));
      });
      saveVideoPlaylists();
      idsToRemove.forEach(id => delete videoPositions[id]);
      appSet("videoPositions", videoPositions);
      videoRecent = videoRecent.filter(e => !idsToRemove.includes(e.id));
      saveVideoRecent();
      renderVideoRecent();
      if (currentVideoId !== null && idsToRemove.includes(currentVideoId)) {
        currentVideoId = null;
        videoCurrentDisplay.textContent = "No video selected";
        videoPlayer.pause();
        videoPlayer.removeAttribute("src");
        playPauseVideoBtn.textContent = "Play";
      }
      loadVideosFromDB();
      renderPlaylistVideos();
      renderVideoPlaylists();
      if (userAccount) userAccount.updateAccountInfo();
    };
    tx.onerror = () => {
      console.error("Failed to delete selected videos", tx.error);
      alert("Could not delete the selected videos.");
    };
  });
})();

playPauseVideoBtn.addEventListener("click", () => {
  if (!currentVideoId && videos.length) return playVideoById(videos[0].id);
  if (videoPlayer.paused) {
    videoPlayer.play();
    playPauseVideoBtn.textContent = "Pause";
  } else {
    videoPlayer.pause();
    playPauseVideoBtn.textContent = "Play";
  }
});

nextVideoBtn.addEventListener("click", () => {
  videoPlaylistPlaying = videoPlaylistPlaying && !!currentVideoPlaylist;
  playNextVideo();
});

prevVideoBtn.addEventListener("click", () => playPrevVideo());

toggleRepeatVideoBtn.addEventListener("click", () => {
  videoRepeat = !videoRepeat;
  videoPlayer.loop = videoRepeat;
  toggleRepeatVideoBtn.textContent = `Repeat: ${videoRepeat ? "On" : "Off"}`;
});

videoPlayer.addEventListener("timeupdate", () => {
  if (!videoPlayer.duration) return;
  videoProgress.value = videoPlayer.currentTime / videoPlayer.duration * 100;
  updateRangeFill(videoProgress);
  videoCurrentTimeEl.textContent = formatTime(videoPlayer.currentTime);
  videoDurationEl.textContent = formatTime(videoPlayer.duration);
  if (currentVideoId !== null) {
    const now = Date.now();
    if (now - lastVideoPositionSave > POSITION_SAVE_INTERVAL) {
      lastVideoPositionSave = now;
      videoPositions[currentVideoId] = videoPlayer.currentTime;
      appSet("videoPositions", videoPositions);
    }
  }
});

videoProgress.addEventListener("input", () => {
  if (videoPlayer.duration) videoPlayer.currentTime = videoProgress.value / 100 * videoPlayer.duration;
  updateRangeFill(videoProgress);
});

videoPlayer.addEventListener("pause", () => {
  if (currentVideoId !== null && videoPlayer.duration) {
    videoPositions[currentVideoId] = videoPlayer.currentTime;
    appSet("videoPositions", videoPositions);
  }
});

videoPlayer.addEventListener("ended", () => {
  if (currentVideoId !== null) {
    delete videoPositions[currentVideoId];
    appSet("videoPositions", videoPositions);
  }
  playNextVideo();
});

document.getElementById("forward-10-video").addEventListener("click", () => {
  videoPlayer.currentTime += 10;
});

document.getElementById("rewind-10-video").addEventListener("click", () => {
  videoPlayer.currentTime = Math.max(0, videoPlayer.currentTime - 10);
});

(function addVideoLoopPlaylistButton() {
  const controls = document.querySelector("#video-page .player-container .controls");
  if (!controls) return;
  const btn = document.createElement("button");
  btn.className = "action-button";
  btn.textContent = "🔁 Loop Playlist: Off";
  controls.insertBefore(btn, controls.firstChild);
  btn.addEventListener("click", () => {
    videoLoopPlaylist = !videoLoopPlaylist;
    btn.textContent = `🔁 Loop Playlist: ${videoLoopPlaylist ? "On" : "Off"}`;
  });
})();

let musicPlaylistMeta = {};

let musicPlaylistSortMode = "name";

function musicPlaylistCtx() {
  return {
    playlistsObj: playlists,
    metaObj: musicPlaylistMeta,
    mediaArray: () => music,
    historyType: "music",
    listEl: playlistsEl,
    toolbarEl: musicPlaylistToolbarEl,
    tracksEl: playlistMusic,
    headerEl: musicPlaylistHeaderEl,
    titleEl: playlistTitle,
    getCurrent: () => currentPlaylist,
    setCurrent: v => {
      currentPlaylist = v;
    },
    getSortMode: () => musicPlaylistSortMode,
    setSortMode: v => {
      musicPlaylistSortMode = v;
      appSet("musicPlaylistSortMode", v);
    },
    saveFn: saveMusicPlaylists,
    saveMetaFn: saveMusicPlaylistMeta,
    renderNamesFn: renderPlaylists,
    renderTracksFn: renderPlaylistMusic,
    selectFn: selectPlaylist,
    playByIdFn: id => playMusicById(id),
    currentPlayingId: () => currentMusicId,
    setPlaying: v => {
      playlistPlaying = v;
    }
  };
}

function renderPlaylists() {
  renderPlaylistNamesGeneric(musicPlaylistCtx());
}

function selectPlaylist(name) {
  currentPlaylist = name;
  if (isSmartPlaylist(name)) {
    playlistTitle.textContent = smartPlaylistLabel(name);
  } else {
    playlistTitle.textContent = name;
  }
  renderPlaylistMusic();
  renderPlaylists();
}

function renderPlaylistMusic() {
  renderPlaylistTracksGeneric(musicPlaylistCtx());
}

document.getElementById("btn-create-playlist").addEventListener("click", () => {
  const name = playlistName.value.trim();
  if (!name || playlists[name] || isSmartPlaylist(name)) return alert("Invalid or duplicate playlist name");
  playlists[name] = [];
  getPlaylistMeta(musicPlaylistMeta, name);
  playlistName.value = "";
  renderPlaylists();
  saveMusicPlaylists();
  saveMusicPlaylistMeta();
});

document.getElementById("btn-delete-playlist").addEventListener("click", () => {
  if (!currentPlaylist || isSmartPlaylist(currentPlaylist)) return alert("Select a playlist first");
  delete playlists[currentPlaylist];
  delete musicPlaylistMeta[currentPlaylist];
  currentPlaylist = null;
  playlistTitle.textContent = "Select a playlist";
  renderPlaylistMusic();
  renderPlaylists();
  saveMusicPlaylists();
  saveMusicPlaylistMeta();
});

document.getElementById("btn-add-selected-to-playlist").addEventListener("click", () => {
  if (!currentPlaylist || isSmartPlaylist(currentPlaylist)) return alert("Select a playlist first");
  document.querySelectorAll("#music-list input[type=checkbox]:checked").forEach(cb => {
    const id = Number(cb.dataset.id);
    if (!playlists[currentPlaylist].includes(id)) playlists[currentPlaylist].push(id);
  });
  touchPlaylistMeta(musicPlaylistMeta, currentPlaylist);
  renderPlaylistMusic();
  renderPlaylists();
  saveMusicPlaylists();
  saveMusicPlaylistMeta();
});

document.getElementById("btn-add-all-to-playlist").addEventListener("click", () => {
  if (!currentPlaylist || isSmartPlaylist(currentPlaylist)) return alert("Select a playlist first");
  music.forEach(song => {
    if (!playlists[currentPlaylist].includes(song.id)) playlists[currentPlaylist].push(song.id);
  });
  touchPlaylistMeta(musicPlaylistMeta, currentPlaylist);
  renderPlaylistMusic();
  renderPlaylists();
  saveMusicPlaylists();
  saveMusicPlaylistMeta();
});

document.getElementById("btn-remove-from-playlist").addEventListener("click", () => {
  if (!currentPlaylist || isSmartPlaylist(currentPlaylist)) return;
  const toRemove = Array.from(playlistMusic.querySelectorAll("input[type=checkbox]:checked")).map(cb => Number(cb.dataset.id));
  playlists[currentPlaylist] = playlists[currentPlaylist].filter(id => !toRemove.includes(id));
  touchPlaylistMeta(musicPlaylistMeta, currentPlaylist);
  renderPlaylistMusic();
  renderPlaylists();
  saveMusicPlaylists();
  saveMusicPlaylistMeta();
});

document.getElementById("btn-clear-playlist").addEventListener("click", () => {
  if (!currentPlaylist || isSmartPlaylist(currentPlaylist)) return;
  playlists[currentPlaylist] = [];
  touchPlaylistMeta(musicPlaylistMeta, currentPlaylist);
  renderPlaylistMusic();
  renderPlaylists();
  saveMusicPlaylists();
  saveMusicPlaylistMeta();
});

document.getElementById("btn-play-playlist").addEventListener("click", () => {
  const ids = getActivePlaylistIds(musicPlaylistCtx());
  if (!currentPlaylist || !ids.length) {
    return alert("Select a playlist with songs");
  }
  playlistPlaying = true;
  playMusicById(ids[0]);
});

function saveMusicPlaylists() {
  appSet("musicPlaylists", playlists);
}

function saveMusicPlaylistMeta() {
  appSet("musicPlaylistMeta", musicPlaylistMeta);
}

(function enablePlaylistPanelDrop(wrapId, isValidId, getCurrentName, addToPlaylist, saveFn, renderListFn, renderNamesFn) {
  const wrap = document.getElementById(wrapId);
  if (!wrap) return;
  wrap.addEventListener("dragover", e => {
    if (!getCurrentName() || !e.dataTransfer.types.includes("text/plain")) return;
    e.preventDefault();
    e.dataTransfer.dropEffect = "copy";
    wrap.classList.add("drag-over");
  });
  wrap.addEventListener("dragleave", e => {
    if (!wrap.contains(e.relatedTarget)) wrap.classList.remove("drag-over");
  });
  wrap.addEventListener("drop", e => {
    e.preventDefault();
    wrap.classList.remove("drag-over");
    const name = getCurrentName();
    if (!name) return;
    const id = Number(e.dataTransfer.getData("text/plain"));
    if (!id || !isValidId(id)) return;
    addToPlaylist(name, id);
    saveFn();
    renderListFn();
    renderNamesFn();
  });
})("playlist-music-wrap", id => !!music.find(s => s.id === id), () => currentPlaylist, (name, id) => {
  if (!playlists[name].includes(id)) playlists[name].push(id);
}, saveMusicPlaylists, renderPlaylistMusic, renderPlaylists);

function enableDragReorder(listEl, onReorder) {
  let draggedLi = null;
  listEl.addEventListener("mousedown", e => {
    const li = e.target.closest("li");
    if (!li || e.target.tagName === "INPUT" || e.target.tagName === "BUTTON") return;
    li.setAttribute("draggable", "true");
  });
  listEl.addEventListener("dragstart", e => {
    draggedLi = e.target.closest("li");
    if (!draggedLi) return;
    draggedLi.classList.add("dragging");
    e.dataTransfer.effectAllowed = "move";
  });
  listEl.addEventListener("dragend", () => {
    if (draggedLi) draggedLi.classList.remove("dragging");
    draggedLi = null;
    listEl.querySelectorAll("li").forEach(li => li.removeAttribute("draggable"));
    const newOrder = Array.from(listEl.children).map(li => Number(li.dataset.id));
    onReorder(newOrder);
  });
  listEl.addEventListener("dragover", e => {
    e.preventDefault();
    if (!draggedLi) return;
    const afterElement = getDragAfterElement(listEl, e.clientY);
    if (afterElement == null) listEl.appendChild(draggedLi); else listEl.insertBefore(draggedLi, afterElement);
  });
  function getDragAfterElement(container, y) {
    const els = [ ...container.querySelectorAll("li:not(.dragging)") ];
    return els.reduce((closest, child) => {
      const box = child.getBoundingClientRect();
      const offset = y - box.top - box.height / 2;
      if (offset < 0 && offset > closest.offset) return {
        offset: offset,
        element: child
      };
      return closest;
    }, {
      offset: Number.NEGATIVE_INFINITY
    }).element;
  }
}

enableDragReorder(playlistMusic, newOrder => {
  if (!currentPlaylist) return;
  playlists[currentPlaylist] = newOrder;
  saveMusicPlaylists();
});

let videoPlaylistMeta = {};

let videoPlaylistSortMode = "name";

function videoPlaylistCtx() {
  return {
    playlistsObj: videoPlaylists,
    metaObj: videoPlaylistMeta,
    mediaArray: () => videos,
    historyType: "video",
    listEl: videoPlaylistsEl,
    toolbarEl: videoPlaylistToolbarEl,
    tracksEl: playlistVideos,
    headerEl: videoPlaylistHeaderEl,
    titleEl: videoPlaylistTitle,
    getCurrent: () => currentVideoPlaylist,
    setCurrent: v => {
      currentVideoPlaylist = v;
    },
    getSortMode: () => videoPlaylistSortMode,
    setSortMode: v => {
      videoPlaylistSortMode = v;
      appSet("videoPlaylistSortMode", v);
    },
    saveFn: saveVideoPlaylists,
    saveMetaFn: saveVideoPlaylistMeta,
    renderNamesFn: renderVideoPlaylists,
    renderTracksFn: renderPlaylistVideos,
    selectFn: selectVideoPlaylist,
    playByIdFn: id => playVideoById(id),
    currentPlayingId: () => currentVideoId,
    setPlaying: v => {
      videoPlaylistPlaying = v;
    }
  };
}

function renderVideoPlaylists() {
  renderPlaylistNamesGeneric(videoPlaylistCtx());
}

function selectVideoPlaylist(name) {
  currentVideoPlaylist = name;
  videoPlaylistTitle.textContent = isSmartPlaylist(name) ? smartPlaylistLabel(name) : name;
  renderPlaylistVideos();
  renderVideoPlaylists();
}

function renderPlaylistVideos() {
  renderPlaylistTracksGeneric(videoPlaylistCtx());
}

document.getElementById("btn-create-video-playlist").addEventListener("click", () => {
  const name = videoPlaylistName.value.trim();
  if (!name || videoPlaylists[name] || isSmartPlaylist(name)) return alert("Invalid or duplicate playlist name");
  videoPlaylists[name] = [];
  getPlaylistMeta(videoPlaylistMeta, name);
  videoPlaylistName.value = "";
  renderVideoPlaylists();
  saveVideoPlaylists();
  saveVideoPlaylistMeta();
});

document.getElementById("btn-delete-video-playlist").addEventListener("click", () => {
  if (!currentVideoPlaylist || isSmartPlaylist(currentVideoPlaylist)) return alert("Select a playlist first");
  delete videoPlaylists[currentVideoPlaylist];
  delete videoPlaylistMeta[currentVideoPlaylist];
  currentVideoPlaylist = null;
  videoPlaylistTitle.textContent = "Select a playlist";
  renderPlaylistVideos();
  renderVideoPlaylists();
  saveVideoPlaylists();
  saveVideoPlaylistMeta();
});

document.getElementById("btn-add-selected-videos-to-playlist").addEventListener("click", () => {
  if (!currentVideoPlaylist || isSmartPlaylist(currentVideoPlaylist)) return alert("Select a video playlist first");
  document.querySelectorAll("#video-list input[type=checkbox]:checked").forEach(cb => {
    const id = Number(cb.dataset.id);
    if (!videoPlaylists[currentVideoPlaylist].includes(id)) videoPlaylists[currentVideoPlaylist].push(id);
  });
  touchPlaylistMeta(videoPlaylistMeta, currentVideoPlaylist);
  renderPlaylistVideos();
  renderVideoPlaylists();
  saveVideoPlaylists();
  saveVideoPlaylistMeta();
});

document.getElementById("btn-add-all-videos-to-playlist").addEventListener("click", () => {
  if (!currentVideoPlaylist || isSmartPlaylist(currentVideoPlaylist)) return alert("Select a video playlist first");
  videos.forEach(v => {
    if (!videoPlaylists[currentVideoPlaylist].includes(v.id)) videoPlaylists[currentVideoPlaylist].push(v.id);
  });
  touchPlaylistMeta(videoPlaylistMeta, currentVideoPlaylist);
  renderPlaylistVideos();
  renderVideoPlaylists();
  saveVideoPlaylists();
  saveVideoPlaylistMeta();
});

document.getElementById("btn-remove-video-from-playlist").addEventListener("click", () => {
  if (!currentVideoPlaylist || isSmartPlaylist(currentVideoPlaylist)) return;
  const toRemove = Array.from(playlistVideos.querySelectorAll("input[type=checkbox]:checked")).map(cb => Number(cb.dataset.id));
  videoPlaylists[currentVideoPlaylist] = videoPlaylists[currentVideoPlaylist].filter(id => !toRemove.includes(id));
  touchPlaylistMeta(videoPlaylistMeta, currentVideoPlaylist);
  renderPlaylistVideos();
  renderVideoPlaylists();
  saveVideoPlaylists();
  saveVideoPlaylistMeta();
});

document.getElementById("btn-clear-video-playlist").addEventListener("click", () => {
  if (!currentVideoPlaylist || isSmartPlaylist(currentVideoPlaylist)) return;
  videoPlaylists[currentVideoPlaylist] = [];
  touchPlaylistMeta(videoPlaylistMeta, currentVideoPlaylist);
  renderPlaylistVideos();
  renderVideoPlaylists();
  saveVideoPlaylists();
  saveVideoPlaylistMeta();
});

document.getElementById("btn-play-video-playlist").addEventListener("click", () => {
  const ids = getActivePlaylistIds(videoPlaylistCtx());
  if (!currentVideoPlaylist || !ids.length) {
    return alert("Select a video playlist with videos");
  }
  videoPlaylistPlaying = true;
  playVideoById(ids[0]);
});

function saveVideoPlaylists() {
  appSet("videoPlaylists", videoPlaylists);
}

function saveVideoPlaylistMeta() {
  appSet("videoPlaylistMeta", videoPlaylistMeta);
}

(function enablePlaylistPanelDrop(wrapId, isValidId, getCurrentName, addToPlaylist, saveFn, renderListFn, renderNamesFn) {
  const wrap = document.getElementById(wrapId);
  if (!wrap) return;
  wrap.addEventListener("dragover", e => {
    if (!getCurrentName() || !e.dataTransfer.types.includes("text/plain")) return;
    e.preventDefault();
    e.dataTransfer.dropEffect = "copy";
    wrap.classList.add("drag-over");
  });
  wrap.addEventListener("dragleave", e => {
    if (!wrap.contains(e.relatedTarget)) wrap.classList.remove("drag-over");
  });
  wrap.addEventListener("drop", e => {
    e.preventDefault();
    wrap.classList.remove("drag-over");
    const name = getCurrentName();
    if (!name) return;
    const id = Number(e.dataTransfer.getData("text/plain"));
    if (!id || !isValidId(id)) return;
    addToPlaylist(name, id);
    saveFn();
    renderListFn();
    renderNamesFn();
  });
})("playlist-videos-wrap", id => !!videos.find(v => v.id === id), () => currentVideoPlaylist, (name, id) => {
  if (!videoPlaylists[name].includes(id)) videoPlaylists[name].push(id);
}, saveVideoPlaylists, renderPlaylistVideos, renderVideoPlaylists);

enableDragReorder(playlistVideos, newOrder => {
  if (!currentVideoPlaylist) return;
  videoPlaylists[currentVideoPlaylist] = newOrder;
  saveVideoPlaylists();
});

function mergeDuplicateMedia(db, storeName, mediaArray, playlistsObj, positions, positionsKey, saveFn, renderTracksFn, renderNamesFn, renderMediaFn, getCurrentId, setCurrentId, silent) {
  if (!db || !currentUserId) {
    if (!silent) alert("Database not ready");
    return;
  }
  const groups = new Map;
  mediaArray.forEach(item => {
    const key = `${item.name.toLowerCase()}|${item.blob.size}`;
    if (!groups.has(key)) groups.set(key, []);
    groups.get(key).push(item);
  });
  const idRemap = new Map;
  const idsToDelete = [];
  groups.forEach(group => {
    if (group.length < 2) return;
    group.sort((a, b) => a.id - b.id);
    const survivor = group[0];
    group.slice(1).forEach(dup => {
      idRemap.set(dup.id, survivor.id);
      idsToDelete.push(dup.id);
    });
  });
  if (!idsToDelete.length) {
    if (!silent) alert("No duplicates found.");
    return;
  }
  const tx = db.transaction(storeName, "readwrite");
  const store = tx.objectStore(storeName);
  idsToDelete.forEach(id => store.delete(id));
  tx.oncomplete = () => {
    Object.keys(playlistsObj).forEach(name => {
      const remapped = playlistsObj[name].map(id => idRemap.get(id) ?? id);
      playlistsObj[name] = [ ...new Set(remapped) ];
    });
    saveFn();
    idsToDelete.forEach(dupId => {
      const survivorId = idRemap.get(dupId);
      if (positions[dupId] !== undefined && positions[survivorId] === undefined) {
        positions[survivorId] = positions[dupId];
      }
      delete positions[dupId];
    });
    if (positionsKey) {
      appSet(positionsKey, positions);
    } else if (db === podcastDB) {
      const txPos = podcastDB.transaction("positions", "readwrite");
      const posStore = txPos.objectStore("positions");
      posStore.clear();
      Object.keys(positions).forEach(id => posStore.put({
        id: Number(id),
        position: positions[id],
        userId: currentUserId
      }));
    }
    const currentId = getCurrentId();
    if (currentId !== null && idRemap.has(currentId)) {
      setCurrentId(idRemap.get(currentId));
    }
    if (silent) {
      console.log(`Automatically merged ${idsToDelete.length} duplicate item(s) in ${storeName}.`);
    } else {
      alert(`Merged ${idsToDelete.length} duplicate(s).`);
    }
    renderMediaFn();
    renderTracksFn();
    renderNamesFn();
    if (userAccount) userAccount.updateAccountInfo();
  };
  tx.onerror = () => {
    console.error("Failed to merge duplicates", tx.error);
    if (!silent) alert("Could not merge duplicates.");
  };
}

function runAutoMergeDuplicates() {
  if (!currentUserId) return;
  mergeDuplicateMedia(musicDB, "music", music, playlists, musicPositions, "musicPositions", saveMusicPlaylists, renderPlaylistMusic, renderPlaylists, () => {
    loadMusicFromDB();
    renderPlaylists();
  }, () => currentMusicId, id => {
    currentMusicId = id;
  }, true);
  mergeDuplicateMedia(videoDB, "videos", videos, videoPlaylists, videoPositions, "videoPositions", saveVideoPlaylists, renderPlaylistVideos, renderVideoPlaylists, () => {
    loadVideosFromDB();
    renderVideoPlaylists();
  }, () => currentVideoId, id => {
    currentVideoId = id;
  }, true);
  mergeDuplicateMedia(podcastDB, "episodes", podcasts, podcastPlaylists, podcastPositions, null, savePodcastPlaylists, renderPodcastPlaylistSongs, renderPodcastPlaylists, () => {
    loadPodcastsFromDB();
    renderPodcastPlaylists();
  }, () => currentPodcastId, id => {
    currentPodcastId = id;
  }, true);
}

function blobToDataURL(blob) {
  return new Promise((resolve, reject) => {
    const reader = new FileReader;
    reader.onload = () => resolve(reader.result);
    reader.onerror = () => reject(reader.error);
    reader.readAsDataURL(blob);
  });
}

async function dataURLToBlob(dataUrl) {
  const res = await fetch(dataUrl);
  return res.blob();
}

const PRISM_PLAYLIST_SIGNATURE = "prism-playlist-export-v1";
const LEGACY_PLAYLIST_SIGNATURE = "lumosphere-playlist-export-v1";

async function exportPlaylistFile(name, idList, mediaArray) {
  if (!name) return alert("Select a playlist first");
  if (!idList || !idList.length) return alert("This playlist has no media to export");
  const zip = new JSZip;
  const manifestItems = [];
  const usedNames = new Set;
  idList.forEach((id, index) => {
    const media = mediaArray.find(m => m.id === id);
    if (!media) return;
    let safeName = media.name.replace(/[\\/:*?"<>|]/g, "_");
    if (usedNames.has(safeName)) safeName = `${index}_${safeName}`;
    usedNames.add(safeName);
    zip.file(`files/${safeName}`, media.blob);
    manifestItems.push({
      file: `files/${safeName}`,
      name: media.name,
      mimeType: media.blob.type
    });
  });
  zip.file("manifest.json", JSON.stringify({
    app: "Prism",
    signature: PRISM_PLAYLIST_SIGNATURE,
    playlistName: name,
    exportedAt: (new Date).toISOString(),
    items: manifestItems
  }));
  const zipBlob = await zip.generateAsync({
    type: "blob"
  });
  const url = URL.createObjectURL(zipBlob);
  const a = document.createElement("a");
  a.href = url;
  a.download = `${name.replace(/[^a-z0-9\-_ ]/gi, "_")}.playlist.zip`;
  document.body.appendChild(a);
  a.click();
  a.remove();
  URL.revokeObjectURL(url);
}

function addMediaToStore(db, storeName, item) {
  return new Promise((resolve, reject) => {
    const tx = db.transaction(storeName, "readwrite");
    const req = tx.objectStore(storeName).add({
      ...item,
      userId: currentUserId
    });
    req.onsuccess = () => resolve(req.result);
    req.onerror = () => reject(req.error);
  });
}

function makeZipPlaylistSource(zip) {
  return {
    async blob(ref) {
      const entry = zip.file(ref);
      return entry ? await entry.async("blob") : null;
    },
    async text(ref) {
      const entry = zip.file(ref);
      return entry ? await entry.async("string") : "";
    },
    has(ref) {
      return !!zip.file(ref);
    }
  };
}

function makeFilesPlaylistSource(files) {
  const map = new Map;
  for (const f of files) {
    const rel = (f.webkitRelativePath || f.name).replace(/^\/+/, "");
    map.set(rel, f);
  }
  return {
    async blob(ref) {
      return map.get(ref) || null;
    },
    async text(ref) {
      const f = map.get(ref);
      return f ? await f.text() : "";
    },
    has(ref) {
      return map.has(ref);
    }
  };
}

async function importPlaylistFromSource(source, payload, db, storeName, mediaArray, playlistsObj, saveFn, renderTracksFn, renderNamesFn, selectFn, metaObj, saveMetaFn, mediaType) {
  if (!db || !currentUserId) return alert("Database not ready");
  if (!payload || !Array.isArray(payload.items) || !payload.items.length) {
    const allowedExt = ZIP_EXTENSIONS_BY_TYPE[mediaType] || [];
    return alert(`No importable files matching the types this terminal supports were found${allowedExt.length ? ` (${allowedExt.join(", ")})` : ""}.`);
  }
  const baseName = (payload.playlistName || "Imported Playlist").trim() || "Imported Playlist";
  let finalName = baseName;
  let suffix = 1;
  if (playlistsObj[baseName]) {
    if (!confirm(`A playlist named "${baseName}" already exists. Import as "${baseName} (${suffix})"?`)) {
      return;
    }
  }
  while (playlistsObj[finalName]) finalName = `${baseName} (${suffix++})`;
  let importItems = payload.items;
  if (storeName === "games") {
    const groups = new Map;
    for (const item of payload.items) {
      if (!item || !item.name || !item.file) continue;
      if (!source.has(item.file)) continue;
      const kind = gameFileKind(item.name);
      const base = gameBaseName(item.name);
      if (!groups.has(base)) groups.set(base, {});
      if (kind === "css") groups.get(base).cssRef = item.file; else if (kind === "js") groups.get(base).jsRef = item.file; else if (kind === "html") {
        groups.get(base).htmlRef = item.file;
        groups.get(base).htmlName = item.name;
      }
    }
    importItems = [];
    for (const [base, group] of groups) {
      if (!group.htmlRef && !group.cssRef && !group.jsRef) continue;
      if (group.cssRef || group.jsRef) {
        const htmlText = group.htmlRef ? await source.text(group.htmlRef) : "<!DOCTYPE html><html><head></head><body></body></html>";
        const cssText = group.cssRef ? await source.text(group.cssRef) : "";
        const jsText = group.jsRef ? await source.text(group.jsRef) : "";
        importItems.push({
          name: group.htmlName || `${base}.html`,
          combinedText: htmlText,
          combinedCss: cssText,
          combinedJs: jsText,
          mimeType: "text/html"
        });
      } else {
        importItems.push({
          file: group.htmlRef,
          name: group.htmlName,
          mimeType: "text/html"
        });
      }
    }
  }
  const ids = [];
  for (const item of importItems) {
    if (!item || !item.name) continue;
    let typedBlob;
    if (item.combinedText !== undefined) {
      let htmlText = item.combinedText;
      if (item.combinedCss) {
        const styleTag = `<style>\n${item.combinedCss}\n</style>`;
        htmlText = /<\/head>/i.test(htmlText) ? htmlText.replace(/<\/head>/i, `${styleTag}\n</head>`) : styleTag + htmlText;
      }
      if (item.combinedJs) {
        const scriptTag = `<script>\n${item.combinedJs}\n<\/script>`;
        htmlText = /<\/body>/i.test(htmlText) ? htmlText.replace(/<\/body>/i, `${scriptTag}\n</body>`) : htmlText + scriptTag;
      }
      typedBlob = new Blob([ htmlText ], {
        type: "text/html"
      });
    } else {
      if (!item.file) continue;
      const blob = await source.blob(item.file);
      if (!blob) continue;
      typedBlob = item.mimeType ? new Blob([ blob ], {
        type: item.mimeType
      }) : blob;
    }
    const existing = mediaArray.find(m => m.name.toLowerCase() === item.name.toLowerCase() && m.blob.size === typedBlob.size);
    if (existing) {
      ids.push(existing.id);
      continue;
    }
    const id = await addMediaToStore(db, storeName, {
      name: item.name,
      blob: typedBlob
    });
    mediaArray.push({
      id: id,
      name: item.name,
      blob: typedBlob,
      userId: currentUserId
    });
    ids.push(id);
  }
  playlistsObj[finalName] = ids;
  if (metaObj) getPlaylistMeta(metaObj, finalName);
  saveFn();
  if (saveMetaFn) saveMetaFn();
  renderNamesFn();
  selectFn(finalName);
  renderTracksFn();
  if (userAccount) userAccount.updateAccountInfo();
  return finalName;
}

async function importPlaylistFile(file, db, storeName, mediaArray, playlistsObj, saveFn, renderTracksFn, renderNamesFn, selectFn, metaObj, saveMetaFn, mediaType) {
  if (!db || !currentUserId) return alert("Database not ready");
  if (typeof JSZip === "undefined") {
    return alert("Zip support failed to load. This is bundled locally and does not require an internet connection - try reloading the page. If it keeps happening, the Prism.js file itself may be corrupted or incomplete.");
  }
  let zip;
  try {
    zip = await loadZipWithRetry(file);
  } catch (err) {
    console.error("Failed to read playlist zip archive", file.name, err);
    return alert(describeZipReadError(file, err));
  }
  const manifestEntry = zip.file("manifest.json");
  let payload = null;
  if (manifestEntry) {
    try {
      payload = JSON.parse(await manifestEntry.async("string"));
    } catch {
      payload = null;
    }
  }
  const isPrismExport = payload && ((payload.app === "Prism" && payload.signature === PRISM_PLAYLIST_SIGNATURE) || (payload.app === "LumoSphere" && payload.signature === LEGACY_PLAYLIST_SIGNATURE));
  if (!payload || !isPrismExport || !Array.isArray(payload.items)) {
    return alert("This zip file wasn't created by Prism's playlist export, so it can't be imported. Only .playlist.zip files exported from Prism are supported.");
  }
  return importPlaylistFromSource(makeZipPlaylistSource(zip), payload, db, storeName, mediaArray, playlistsObj, saveFn, renderTracksFn, renderNamesFn, selectFn, metaObj, saveMetaFn, mediaType);
}

function buildPlaylistPayloadFromFolderFiles(files, fallbackName, mediaType) {
  const allowedExt = ZIP_EXTENSIONS_BY_TYPE[mediaType] || null;
  const items = [];
  const entries = [ ...files ].filter(f => {
    const rel = f.webkitRelativePath || f.name;
    if (isHiddenOrSystemEntryPath(rel)) return false;
    if (isZipFile(f)) return false;
    const shortName = rel.split("/").pop();
    return shortName && shortName.toLowerCase() !== "manifest.json";
  }).sort((a, b) => (a.webkitRelativePath || a.name).localeCompare(b.webkitRelativePath || b.name));
  for (const f of entries) {
    const rel = (f.webkitRelativePath || f.name).replace(/^\/+/, "");
    const shortName = rel.split("/").pop();
    const ext = (shortName.split(".").pop() || "").toLowerCase();
    if (allowedExt && !allowedExt.includes(ext)) continue;
    items.push({
      file: rel,
      name: shortName,
      mimeType: guessMimeTypeFromName(shortName)
    });
  }
  return {
    playlistName: fallbackName,
    items: items
  };
}

async function importPlaylistFolder(files, folderName, db, storeName, mediaArray, playlistsObj, saveFn, renderTracksFn, renderNamesFn, selectFn, metaObj, saveMetaFn, mediaType) {
  if (!db || !currentUserId) return alert("Database not ready");
  if (!files || !files.length) return;
  const payload = buildPlaylistPayloadFromFolderFiles(files, folderName, mediaType);
  return importPlaylistFromSource(makeFilesPlaylistSource(files), payload, db, storeName, mediaArray, playlistsObj, saveFn, renderTracksFn, renderNamesFn, selectFn, metaObj, saveMetaFn, mediaType);
}

if (exportPlaylistBtn) {
  exportPlaylistBtn.addEventListener("click", () => {
    exportPlaylistFile(currentPlaylist, currentPlaylist ? getActivePlaylistIds(musicPlaylistCtx()) : null, music);
  });
}

PLAYLIST_FOLDER_IMPORT_HANDLERS["playlist-import"] = async (files, folderName) => {
  await importPlaylistFolder(files, folderName, musicDB, "music", music, playlists, saveMusicPlaylists, renderPlaylistMusic, renderPlaylists, selectPlaylist, musicPlaylistMeta, saveMusicPlaylistMeta, "audio");
  renderMusic(musicSearch.value);
};

if (playlistImportInput) {
  playlistImportInput.addEventListener("change", async e => {
    const file = e.target.files[0];
    if (!file) return;
    try {
      await importPlaylistFile(file, musicDB, "music", music, playlists, saveMusicPlaylists, renderPlaylistMusic, renderPlaylists, selectPlaylist, musicPlaylistMeta, saveMusicPlaylistMeta, "audio");
    } finally {
      e.target.value = "";
    }
    renderMusic(musicSearch.value);
  });
}

if (exportVideoPlaylistBtn) {
  exportVideoPlaylistBtn.addEventListener("click", () => {
    exportPlaylistFile(currentVideoPlaylist, currentVideoPlaylist ? getActivePlaylistIds(videoPlaylistCtx()) : null, videos);
  });
}

PLAYLIST_FOLDER_IMPORT_HANDLERS["video-playlist-import"] = async (files, folderName) => {
  await importPlaylistFolder(files, folderName, videoDB, "videos", videos, videoPlaylists, saveVideoPlaylists, renderPlaylistVideos, renderVideoPlaylists, selectVideoPlaylist, videoPlaylistMeta, saveVideoPlaylistMeta, "video");
  renderVideos(videoSearch.value);
};

if (videoPlaylistImportInput) {
  videoPlaylistImportInput.addEventListener("change", async e => {
    const file = e.target.files[0];
    if (!file) return;
    try {
      await importPlaylistFile(file, videoDB, "videos", videos, videoPlaylists, saveVideoPlaylists, renderPlaylistVideos, renderVideoPlaylists, selectVideoPlaylist, videoPlaylistMeta, saveVideoPlaylistMeta, "video");
    } finally {
      e.target.value = "";
    }
    renderVideos(videoSearch.value);
  });
}

let historyData = null;

let historyReady = false;

const historyCache = new Map;

function openHistoryStore() {
  return openIndexedDBSafely("HistoryStoreDB", 1, e => {
    const db = e.target.result;
    if (!db.objectStoreNames.contains("kv")) db.createObjectStore("kv");
  });
}

function historyBufferKey() {
  return currentUserId ? `history_data_u${currentUserId}` : "history_data";
}

function loadHistoryBuffer() {
  return openHistoryStore().then(db => new Promise(resolve => {
    const tx = db.transaction("kv", "readonly");
    const req = tx.objectStore("kv").get(historyBufferKey());
    req.onsuccess = () => resolve(req.result || null);
    req.onerror = () => resolve(null);
  }));
}

function saveHistoryBuffer() {
  if (!historyData) return;
  openHistoryStore().then(db => {
    const tx = db.transaction("kv", "readwrite");
    tx.objectStore("kv").put(historyData, historyBufferKey());
  });
}

async function initHistory() {
  try {
    const saved = await loadHistoryBuffer();
    historyData = saved && Array.isArray(saved.play_log) ? saved : {
      play_log: [],
      account_events: [],
      nextPlayId: 1,
      nextEventId: 1
    };
    if (!Array.isArray(historyData.account_events)) historyData.account_events = [];
    if (typeof historyData.nextPlayId !== "number") historyData.nextPlayId = historyData.play_log.reduce((m, r) => Math.max(m, r.id || 0), 0) + 1;
    if (typeof historyData.nextEventId !== "number") historyData.nextEventId = historyData.account_events.reduce((m, r) => Math.max(m, r.id || 0), 0) + 1;
    saveHistoryBuffer();
    historyReady = true;
    refreshHistoryCache();
    renderMusicHistory();
    renderVideoHistory();
    renderPodcastHistory();
    renderBookmarkHistory();
    renderMusic(musicSearch.value);
    renderVideos(videoSearch.value);
    renderPodcasts(podcastSearch.value);
  } catch (err) {
    console.error("Play history unavailable:", err);
    historyReady = false;
    renderMusicHistory();
    renderVideoHistory();
    renderPodcastHistory();
    renderBookmarkHistory();
  }
}

function refreshHistoryCache() {
  historyCache.clear();
  if (!historyReady) return;
  historyData.play_log.forEach(row => {
    const key = `${row.media_type}|${row.media_name}`;
    const entry = historyCache.get(key) || {
      count: 0,
      last: null
    };
    entry.count += 1;
    if (!entry.last || row.played_at > entry.last) entry.last = row.played_at;
    historyCache.set(key, entry);
  });
}

function getPlayCount(type, name) {
  const entry = historyCache.get(`${type}|${name}`);
  return entry ? entry.count : 0;
}

function recordPlay(mediaType, mediaName, source) {
  if (!historyReady || !historyData) return;
  const now = (new Date).toLocaleString();
  historyData.play_log.push({
    id: historyData.nextPlayId++,
    media_type: mediaType,
    media_name: mediaName,
    source: source || "Library",
    played_at: now
  });
  saveHistoryBuffer();
  refreshHistoryCache();
  if (mediaType === "music") renderMusicHistory(); else if (mediaType === "video") renderVideoHistory(); else if (mediaType === "podcast") renderPodcastHistory(); else if (mediaType === "bookmark") renderBookmarkHistory();
}

async function logAccountEventForUser(userId, eventType, detail = "") {
  if (userId === currentUserId) {
    logAccountEvent(userId, eventType, detail);
    return;
  }
  const prevUserId = currentUserId, prevReady = historyReady, prevData = historyData;
  try {
    currentUserId = userId;
    await initHistory();
    logAccountEvent(userId, eventType, detail);
  } finally {
    currentUserId = prevUserId;
    historyReady = prevReady;
    historyData = prevData;
    refreshHistoryCache();
    renderMusicHistory();
    renderVideoHistory();
    renderPodcastHistory();
    renderBookmarkHistory();
  }
}

function logAccountEvent(userId, eventType, detail = "") {
  if (!historyReady || !historyData || !userId) return;
  historyData.account_events.push({
    id: historyData.nextEventId++,
    user_id: String(userId),
    event_type: eventType,
    detail: detail,
    occurred_at: (new Date).toISOString()
  });
  saveHistoryBuffer();
}

function getAccountEventCount(userId, eventType, sinceDate) {
  if (!historyReady || !historyData || !userId) return 0;
  const sinceIso = sinceDate.toISOString();
  return historyData.account_events.filter(e => e.user_id === String(userId) && e.event_type === eventType && e.occurred_at >= sinceIso).length;
}

function getAccountEvents(userId, limit = 100) {
  if (!historyReady || !historyData || !userId) return [];
  return historyData.account_events
    .filter(e => e.user_id === String(userId))
    .sort((a, b) => (a.occurred_at < b.occurred_at ? 1 : a.occurred_at > b.occurred_at ? -1 : 0))
    .slice(0, limit)
    .map(e => ({
      eventType: e.event_type,
      detail: e.detail,
      occurredAt: e.occurred_at
    }));
}

function getAccountActivitySummary(userId) {
  const now = Date.now();
  return {
    loginsLast7Days: getAccountEventCount(userId, "login", new Date(now - 7 * 864e5)),
    loginsLast30Days: getAccountEventCount(userId, "login", new Date(now - 30 * 864e5)),
    loginsAllTime: getAccountEventCount(userId, "login", new Date(0))
  };
}

function exportAccountActivity(userId, username) {
  const totals = getAccountActivitySummary(userId);
  const events = getAccountEvents(userId, 1e3);
  const report = {
    version: 1,
    userId: String(userId),
    generatedAt: (new Date).toISOString(),
    totals: totals,
    events: events
  };
  const blob = new Blob([ JSON.stringify(report, null, 2) ], {
    type: "application/json"
  });
  const a = document.createElement("a");
  a.href = URL.createObjectURL(blob);
  a.download = `prism-activity-${username || userId}.json`;
  document.body.appendChild(a);
  a.click();
  a.remove();
  URL.revokeObjectURL(a.href);
}

function renderAccountActivitySummary(userId) {
  const el7 = document.getElementById("account-logins-7d");
  const el30 = document.getElementById("account-logins-30d");
  const elAll = document.getElementById("account-logins-all");
  if (!el7 && !el30 && !elAll) return;
  const totals = getAccountActivitySummary(userId);
  if (el7) el7.textContent = String(totals.loginsLast7Days);
  if (el30) el30.textContent = String(totals.loginsLast30Days);
  if (elAll) elAll.textContent = String(totals.loginsAllTime);
}

function removeHistoryEntry(id, mediaType) {
  if (!historyReady || !historyData) return;
  historyData.play_log = historyData.play_log.filter(row => row.id !== id);
  saveHistoryBuffer();
  refreshHistoryCache();
  if (mediaType === "music") {
    renderMusicHistory();
    renderMusic(musicSearch.value);
  } else if (mediaType === "video") {
    renderVideoHistory();
    renderVideos(videoSearch.value);
  } else if (mediaType === "podcast") {
    renderPodcastHistory();
    renderPodcasts(podcastSearch.value);
  }
}

const HISTORY_TYPE_ICONS = {
  music: "🎵",
  video: "🎬",
  podcast: "🎙️",
  bookmark: "🔖"
};

function buildHistoryRow({mediaType: mediaType, title: title, metaParts: metaParts, removeClass: removeClass, onRemove: onRemove, empty: empty}) {
  const li = document.createElement("li");
  if (empty) {
    li.className = `${removeClass === "recent-remove-btn" ? "recent-item" : "history-item"} list-empty-state`;
    li.textContent = title;
    return li;
  }
  li.className = removeClass === "recent-remove-btn" ? "recent-item" : "history-item";
  const iconEl = document.createElement("span");
  iconEl.className = "history-icon";
  iconEl.textContent = HISTORY_TYPE_ICONS[mediaType] || "🎵";
  const bodyEl = document.createElement("div");
  bodyEl.className = "history-item-body";
  const titleEl = document.createElement("span");
  titleEl.className = "history-item-title";
  titleEl.textContent = title;
  titleEl.title = title;
  bodyEl.appendChild(titleEl);
  const metaEl = document.createElement("div");
  metaEl.className = "history-item-meta";
  metaParts.forEach(part => {
    if (!part) return;
    const span = document.createElement("span");
    span.className = part.className;
    span.textContent = part.text;
    metaEl.appendChild(span);
  });
  bodyEl.appendChild(metaEl);
  const removeBtn = document.createElement("button");
  removeBtn.className = removeClass;
  removeBtn.innerHTML = "&times;";
  removeBtn.setAttribute("aria-label", "Remove entry");
  removeBtn.addEventListener("click", onRemove);
  li.append(iconEl, bodyEl, removeBtn);
  return li;
}

const HISTORY_TERMINAL_LABELS = {
  music: "Music Terminal",
  video: "Video Terminal",
  podcast: "Podcast Terminal",
  bookmark: "Bookmark Terminal",
  documentary: "Documentary Terminal",
  movie: "Movie Terminal",
  comedy: "Comedy Terminal",
  webseries: "Web Series Terminal",
  games: "Game Terminal",
  books: "Book Terminal",
  gamevideo: "Game Video Terminal",
  gamemovie: "Game Movie Terminal",
  bookvideo: "Book Video Terminal",
  bookmovie: "Book Movie Terminal",
  presentations: "Presentations Terminal"
};

function renderHistoryList(el, mediaType) {
  if (!el) return;
  el.innerHTML = "";
  if (!historyReady) {
    const li = document.createElement("li");
    li.className = "history-item";
    li.textContent = "History unavailable";
    el.appendChild(li);
    return;
  }
  const rows = historyData.play_log
    .filter(row => row.media_type === mediaType)
    .sort((a, b) => b.id - a.id)
    .slice(0, 50)
    .map(row => [ row.id, row.media_name, row.source, row.played_at ]);
  if (!rows.length) {
    const terminalLabel = HISTORY_TERMINAL_LABELS[mediaType] || "this Terminal";
    el.appendChild(buildHistoryRow({
      empty: true,
      title: `No recent plays in ${terminalLabel}.`,
      removeClass: "history-remove-btn"
    }));
    return;
  }
  rows.forEach(([id, name, source, playedAt]) => {
    el.appendChild(buildHistoryRow({
      mediaType: mediaType,
      title: name,
      metaParts: [ {
        className: "history-source",
        text: `▸ ${source || "Library"}`
      }, {
        className: "history-timestamp",
        text: playedAt || ""
      } ],
      removeClass: "history-remove-btn",
      onRemove: () => removeHistoryEntry(id, mediaType)
    }));
  });
}

function renderMusicHistory() {
  renderHistoryList(document.getElementById("music-history-list"), "music");
}

function renderVideoHistory() {
  renderHistoryList(document.getElementById("video-history-list"), "video");
}

function renderPodcastHistory() {
  renderHistoryList(document.getElementById("podcast-history-list"), "podcast");
}

document.getElementById("btn-clear-music-history")?.addEventListener("click", () => {
  if (!historyReady) return;
  historyData.play_log = historyData.play_log.filter(row => row.media_type !== "music");
  saveHistoryBuffer();
  refreshHistoryCache();
  renderMusicHistory();
  renderMusic(musicSearch.value);
});

document.getElementById("btn-clear-video-history")?.addEventListener("click", () => {
  if (!historyReady) return;
  historyData.play_log = historyData.play_log.filter(row => row.media_type !== "video");
  saveHistoryBuffer();
  refreshHistoryCache();
  renderVideoHistory();
  renderVideos(videoSearch.value);
});

document.getElementById("btn-clear-podcast-history")?.addEventListener("click", () => {
  if (!historyReady) return;
  historyData.play_log = historyData.play_log.filter(row => row.media_type !== "podcast");
  saveHistoryBuffer();
  refreshHistoryCache();
  renderPodcastHistory();
  renderPodcasts(podcastSearch.value);
});

function downloadMusicRecent() {
  const sorted = [ ...musicRecent ].map(e => e.name).sort();
  const content = sorted.join("\n");
  const blob = new Blob([ content ], {
    type: "text/plain"
  });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = "music_recently_added.txt";
  a.click();
  URL.revokeObjectURL(url);
}

function downloadMusicHistory() {
  if (!historyReady) return;
  const names = [ ...new Set(historyData.play_log.filter(row => row.media_type === "music").map(row => row.media_name)) ].sort();
  const content = names.join("\n");
  const blob = new Blob([ content ], {
    type: "text/plain"
  });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = "music_history.txt";
  a.click();
  URL.revokeObjectURL(url);
}

function downloadVideoRecent() {
  const sorted = [ ...videoRecent ].map(e => e.name).sort();
  const content = sorted.join("\n");
  const blob = new Blob([ content ], {
    type: "text/plain"
  });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = "video_recently_added.txt";
  a.click();
  URL.revokeObjectURL(url);
}

function downloadVideoHistory() {
  if (!historyReady) return;
  const names = [ ...new Set(historyData.play_log.filter(row => row.media_type === "video").map(row => row.media_name)) ].sort();
  const content = names.join("\n");
  const blob = new Blob([ content ], {
    type: "text/plain"
  });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = "video_history.txt";
  a.click();
  URL.revokeObjectURL(url);
}

function downloadPodcastRecent() {
  const sorted = [ ...podcastRecent ].map(e => e.name).sort();
  const content = sorted.join("\n");
  const blob = new Blob([ content ], {
    type: "text/plain"
  });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = "podcast_recently_added.txt";
  a.click();
  URL.revokeObjectURL(url);
}

function downloadPodcastHistory() {
  if (!historyReady) return;
  const names = [ ...new Set(historyData.play_log.filter(row => row.media_type === "podcast").map(row => row.media_name)) ].sort();
  const content = names.join("\n");
  const blob = new Blob([ content ], {
    type: "text/plain"
  });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = "podcast_history.txt";
  a.click();
  URL.revokeObjectURL(url);
}

document.getElementById("btn-download-music-recent")?.addEventListener("click", downloadMusicRecent);

document.getElementById("btn-download-music-history")?.addEventListener("click", downloadMusicHistory);

document.getElementById("btn-download-video-recent")?.addEventListener("click", downloadVideoRecent);

document.getElementById("btn-download-video-history")?.addEventListener("click", downloadVideoHistory);

document.getElementById("btn-download-podcast-recent")?.addEventListener("click", downloadPodcastRecent);

document.getElementById("btn-download-podcast-history")?.addEventListener("click", downloadPodcastHistory);

let podcasts = [];

let podcastPlaylists = {};

let currentPodcastPlaylist = null;

let currentPodcastId = null;

let podcastRepeat = false;

let podcastLoopPlaylist = false;

let podcastPlaylistPlaying = false;

let podcastPositions = {};

let podcastDB;

let lastPodcastPositionSave = 0;

let podcastRecent = [];

const podcastUpload = document.getElementById("podcast-upload");

const podcastList = document.getElementById("podcast-list");

const podcastCount = document.getElementById("podcast-count");

const podcastSearch = document.getElementById("podcast-search");

const podcastPlayer = document.getElementById("podcast-player");

const currentPodcastDisplay = document.getElementById("current-podcast");

const playPausePodcastBtn = document.getElementById("play-pause-podcast");

const nextPodcastBtn = document.getElementById("next-podcast");

const prevPodcastBtn = document.getElementById("prev-podcast");

const toggleRepeatPodcastBtn = document.getElementById("toggle-repeat-podcast");

const podcastProgress = document.getElementById("podcast-progress");

const podcastCurrentTimeEl = document.getElementById("podcast-current-time");

const podcastDurationEl = document.getElementById("podcast-duration");

const podcastPlaylistName = document.getElementById("podcast-playlist-name");

const podcastPlaylistsEl = document.getElementById("podcast-playlists");

const playlistPodcastSongs = document.getElementById("podcast-playlist-songs");

const podcastPlaylistTitle = document.getElementById("podcast-playlist-title");

const podcastPlaylistHeaderEl = document.getElementById("podcast-playlist-header");

const podcastPlaylistToolbarEl = document.getElementById("podcast-playlist-toolbar");

const podcastVolume = document.getElementById("podcast-volume");

const podcastMuteBtn = document.getElementById("podcast-mute-btn");

const podcastVolumeLabel = document.getElementById("podcast-volume-label");

const podcastSpeedGroup = document.getElementById("podcast-speed-group");

const exportPodcastPlaylistBtn = document.getElementById("btn-export-podcast-playlist");

const podcastPlaylistImportInput = document.getElementById("podcast-playlist-import");

const selectAllPodcastsCheckbox = document.getElementById("select-all-podcasts");

const deleteSelectedPodcastsBtn = document.getElementById("btn-delete-selected-podcasts");

const podcastRecentList = document.getElementById("podcast-recent-list");

const clearPodcastRecentBtn = document.getElementById("btn-clear-podcast-recent");

function openPodcastDB() {
  return openTerminalDB("PodcastDB", [ {
    name: "episodes"
  }, {
    name: "playlists",
    options: {
      keyPath: "name"
    }
  }, {
    name: "positions",
    options: {
      keyPath: "id"
    }
  } ]);
}

async function loadPodcastEpisodes() {
  if (!podcastDB || !currentUserId) return;
  const rows = await loadUserRecordsIndexed(podcastDB, "episodes", currentUserId);
  podcasts.length = 0;
  podcasts.push(...rows);
}

function loadPodcastPlaylistsAsync() {
  return new Promise(resolve => {
    if (!podcastDB || !currentUserId) return resolve();
    const tx = podcastDB.transaction("playlists", "readonly");
    const store = tx.objectStore("playlists");
    const req = store.getAll();
    req.onsuccess = () => {
      podcastPlaylists = {};
      req.result.filter(item => item.userId === currentUserId).forEach(item => {
        podcastPlaylists[item.name] = item.songs || [];
      });
      resolve();
    };
    req.onerror = () => resolve();
  });
}

function loadPodcastPositionsAsync() {
  return new Promise(resolve => {
    if (!podcastDB || !currentUserId) return resolve();
    const tx = podcastDB.transaction("positions", "readonly");
    const store = tx.objectStore("positions");
    const req = store.getAll();
    req.onsuccess = () => {
      podcastPositions = {};
      req.result.filter(item => item.userId === currentUserId).forEach(item => {
        podcastPositions[item.id] = item.position;
      });
      resolve();
    };
    req.onerror = () => resolve();
  });
}

async function loadPodcastsFromDB() {
  if (!podcastDB || !currentUserId) {
    podcasts.length = 0;
    renderPodcasts(podcastSearch.value);
    return;
  }
  podcastPlaylistMeta = appGet("podcastPlaylistMeta", {});
  await Promise.all([ loadPodcastEpisodes(), loadPodcastPlaylistsAsync(), loadPodcastPositionsAsync() ]);
  restoreListSortMode("podcast", podcasts);
  renderPodcasts(podcastSearch.value);
  renderPodcastPlaylists();
  if (currentPodcastId && podcastPositions[currentPodcastId]) {
    const episode = podcasts.find(e => e.id === currentPodcastId);
    if (episode) {
      currentPodcastDisplay.textContent = episode.name;
    }
  }
  if (userAccount) userAccount.updateAccountInfo();
}

function renderPodcasts(filter = "") {
  const f = filter.toLowerCase();
  const visible = podcasts.filter(episode => !f || episode.name.toLowerCase().includes(f));
  renderListBatched(podcastList, visible, episode => {
    const li = document.createElement("li");
    if (episode.id === currentPodcastId) li.classList.add("selected");
    const cb = document.createElement("input");
    cb.type = "checkbox";
    cb.dataset.id = episode.id;
    cb.addEventListener("change", () => {
      li.classList.toggle("selected", cb.checked);
      const allChecked = Array.from(document.querySelectorAll("#podcast-list input[type=checkbox]")).every(c => c.checked);
      if (selectAllPodcastsCheckbox) selectAllPodcastsCheckbox.checked = allChecked;
    });
    const name = document.createElement("span");
    const count = getPlayCount("podcast", episode.name);
    name.textContent = count > 0 ? `${episode.name}  ·  ${count} play${count === 1 ? "" : "s"}` : episode.name;
    const playBtn = document.createElement("button");
    playBtn.textContent = "▶";
    playBtn.className = "media-row-play-btn";
    playBtn.addEventListener("click", () => {
      podcastPlaylistPlaying = false;
      currentPodcastPlaylist = null;
      playPodcastById(episode.id);
    });
    li.append(cb, name, playBtn);
    attachPodcastDragSource(li, episode);
    attachRowClickToggle(li, cb, playBtn);
    return li;
  });
  podcastCount.textContent = `${podcasts.length}`;
}

function attachPodcastDragSource(li, episode) {
  li.draggable = true;
  li.addEventListener("dragstart", e => {
    e.dataTransfer.setData("text/plain", String(episode.id));
    e.dataTransfer.effectAllowed = "copy";
    li.classList.add("dragging");
  });
  li.addEventListener("dragend", () => li.classList.remove("dragging"));
}

function savePodcastPosition(id, position) {
  podcastPositions[id] = position;
  if (!podcastDB || !currentUserId) return;
  const tx = podcastDB.transaction("positions", "readwrite");
  tx.objectStore("positions").put({
    id: id,
    position: position,
    userId: currentUserId
  });
}

function deletePodcastPosition(id) {
  delete podcastPositions[id];
  if (!podcastDB) return;
  const tx = podcastDB.transaction("positions", "readwrite");
  tx.objectStore("positions").delete(id);
}

function playPodcastById(id, isResume) {
  const episode = podcasts.find(e => e.id === id);
  if (!episode) return;
  let url;
  try {
    url = URL.createObjectURL(episode.blob);
  } catch (err) {
    console.error("Failed to create a playback URL for this episode", err);
    alert("Could not load this episode for playback.");
    return;
  }
  currentPodcastId = id;
  if (podcastPlayer.dataset.url) URL.revokeObjectURL(podcastPlayer.dataset.url);
  podcastPlayer.src = url;
  podcastPlayer.dataset.url = url;
  const resumeAt = podcastPositions[id];
  if (resumeAt) {
    const restorePosition = () => {
      if (resumeAt < podcastPlayer.duration - 2) podcastPlayer.currentTime = resumeAt;
      podcastPlayer.removeEventListener("loadedmetadata", restorePosition);
    };
    podcastPlayer.addEventListener("loadedmetadata", restorePosition);
  }
  currentPodcastDisplay.textContent = episode.name;
  appSet("lastPodcastId", id);
  if (isResume) {
    playPausePodcastBtn.textContent = "Play";
  } else {
    podcastPlayer.play().then(() => {
      playPausePodcastBtn.textContent = "Pause";
    }).catch(err => {
      console.error("Playback failed to start", err);
      playPausePodcastBtn.textContent = "Play";
    });
  }
  if (!isResume) recordPlay("podcast", episode.name, currentPodcastSource());
  renderPodcasts(podcastSearch.value);
  renderPodcastPlaylistSongs();
}

function currentPodcastSource() {
  return podcastPlaylistPlaying && currentPodcastPlaylist ? `Playlist: ${isSmartPlaylist(currentPodcastPlaylist) ? smartPlaylistLabel(currentPodcastPlaylist) : currentPodcastPlaylist}` : "Library";
}

function playNextPodcast() {
  const queuedId = consumeQueueNext("podcast");
  if (queuedId !== null) return playPodcastById(queuedId);
  if (podcastPlaylistPlaying && currentPodcastPlaylist) {
    const list = getActivePlaylistIds(podcastPlaylistCtx());
    const shuffle = !isSmartPlaylist(currentPodcastPlaylist) && getPlaylistMeta(podcastPlaylistMeta, currentPodcastPlaylist).shuffle;
    const next = pickNextInList(list, currentPodcastId, shuffle);
    if (next !== null) return playPodcastById(next);
    if (podcastLoopPlaylist && list.length) return playPodcastById(shuffle ? list[Math.floor(Math.random() * list.length)] : list[0]);
    podcastPlaylistPlaying = false;
    return;
  }
  if (!podcasts.length) return;
  const idx = podcasts.findIndex(e => e.id === currentPodcastId);
  const nextIdx = idx === -1 ? 0 : (idx + 1) % podcasts.length;
  playPodcastById(podcasts[nextIdx].id);
}

function playPrevPodcast() {
  if (podcastPlaylistPlaying && currentPodcastPlaylist) {
    const list = getActivePlaylistIds(podcastPlaylistCtx());
    const idx = list.indexOf(currentPodcastId);
    if (idx > 0) return playPodcastById(list[idx - 1]);
    return;
  }
  if (!podcasts.length) return;
  const idx = podcasts.findIndex(e => e.id === currentPodcastId);
  const prevIdx = idx <= 0 ? podcasts.length - 1 : idx - 1;
  playPodcastById(podcasts[prevIdx].id);
}

function savePodcastRecent() {
  appSet("podcastRecent", podcastRecent);
}

function renderPodcastRecent() {
  if (!podcastRecentList) return;
  podcastRecentList.innerHTML = "";
  const sorted = [ ...podcastRecent ].sort((a, b) => b.addedAt - a.addedAt);
  if (!sorted.length) {
    podcastRecentList.appendChild(buildHistoryRow({
      empty: true,
      title: "No recent uploads in Podcast Terminal.",
      removeClass: "recent-remove-btn"
    }));
    return;
  }
  sorted.forEach(entry => {
    podcastRecentList.appendChild(buildHistoryRow({
      mediaType: "podcast",
      title: entry.name,
      metaParts: [ {
        className: "history-timestamp",
        text: new Date(entry.addedAt).toLocaleString()
      } ],
      removeClass: "recent-remove-btn",
      onRemove: () => {
        podcastRecent = podcastRecent.filter(e => e.entryId !== entry.entryId);
        savePodcastRecent();
        renderPodcastRecent();
      }
    }));
  });
}

if (clearPodcastRecentBtn) {
  clearPodcastRecentBtn.addEventListener("click", () => {
    podcastRecent = [];
    savePodcastRecent();
    renderPodcastRecent();
  });
}

podcastUpload.addEventListener("change", async e => {
  if (!podcastDB || !currentUserId) return;
  const rawFiles = [ ...e.target.files ];
  if (!rawFiles.length) return;
  const files = filterUploadedMediaFiles(rawFiles, "audio");
  if (!files.length) {
    podcastUpload.value = "";
    return;
  }
  const totalSize = files.reduce((sum, f) => sum + f.size, 0);
  if (files.length > 200 || totalSize > 2 * 1024 * 1024 * 1024) {
    const totalMB = Math.round(totalSize / (1024 * 1024));
    if (!confirm(`You're uploading ${files.length} file(s) (~${totalMB} MB total). Large batches can use a lot of browser memory. Continue?`)) {
      podcastUpload.value = "";
      return;
    }
  }
  const progressEl = document.createElement("div");
  progressEl.style.cssText = "position:fixed;bottom:20px;left:50%;transform:translateX(-50%);background:rgba(0,0,0,0.9);padding:15px 25px;border-radius:10px;color:#fff;z-index:99999;font-family:Inter,sans-serif;";
  progressEl.textContent = `Uploading ${files.length} files...`;
  document.body.appendChild(progressEl);
  const existingKeys = new Set(podcasts.map(p => `${p.name.toLowerCase()}|${p.blob.size}`));
  const newFiles = files.filter(f => !existingKeys.has(`${f.name.toLowerCase()}|${f.size}`));
  const skippedCount = files.length - newFiles.length;
  if (!newFiles.length) {
    podcastUpload.value = "";
    progressEl.remove();
    if (skippedCount) alert(`Skipped ${skippedCount} duplicate podcast(s) already in your library.`);
    return;
  }
  const tx = podcastDB.transaction("episodes", "readwrite");
  const store = tx.objectStore("episodes");
  const addedEntries = [];
  newFiles.forEach(file => {
    const req = store.add({
      name: file.name,
      blob: file,
      userId: currentUserId
    });
    req.onsuccess = () => {
      addedEntries.push({
        entryId: `p${req.result}_${Date.now()}_${Math.random().toString(36).slice(2)}`,
        id: req.result,
        name: file.name,
        addedAt: Date.now()
      });
    };
  });
  tx.oncomplete = () => {
    podcastUpload.value = "";
    progressEl.remove();
    podcastRecent = podcastRecent.concat(addedEntries);
    savePodcastRecent();
    renderPodcastRecent();
    loadPodcastsFromDB();
    if (skippedCount) alert(`Added ${newFiles.length} podcast(s). Skipped ${skippedCount} duplicate(s).`);
  };
  tx.onerror = () => {
    console.error("Failed to save uploaded podcast(s)", tx.error);
    progressEl.remove();
    alert("Could not save the uploaded podcast file(s).");
  };
});

selectAllPodcastsCheckbox?.addEventListener("change", () => {
  const checked = selectAllPodcastsCheckbox.checked;
  podcastList.querySelectorAll("li").forEach(li => {
    const cb = li.querySelector("input[type=checkbox]");
    if (!cb) return;
    cb.checked = checked;
    li.classList.toggle("selected", checked);
  });
});

podcastSearch.addEventListener("input", debounce(() => renderPodcasts(podcastSearch.value)));

document.getElementById("btn-shuffle-podcasts").addEventListener("click", () => {
  shuffleArray(podcasts);
  saveListSortMode("podcast", "shuffle", podcasts);
  renderPodcasts(podcastSearch.value);
});

document.getElementById("btn-sort-az-podcasts").addEventListener("click", () => {
  podcasts.sort((a, b) => a.name.localeCompare(b.name));
  saveListSortMode("podcast", "az", podcasts);
  renderPodcasts(podcastSearch.value);
});

document.getElementById("btn-sort-za-podcasts").addEventListener("click", () => {
  podcasts.sort((a, b) => b.name.localeCompare(a.name));
  saveListSortMode("podcast", "za", podcasts);
  renderPodcasts(podcastSearch.value);
});

if (deleteSelectedPodcastsBtn) {
  deleteSelectedPodcastsBtn.addEventListener("click", () => {
    if (!podcastDB) return alert("Database not ready");
    const selected = document.querySelectorAll("#podcast-list input[type=checkbox]:checked");
    if (selected.length === 0) return alert("No podcasts selected");
    const idsToRemove = Array.from(selected).map(cb => Number(cb.dataset.id)).filter(id => !isNaN(id));
    const tx = podcastDB.transaction("episodes", "readwrite");
    const store = tx.objectStore("episodes");
    idsToRemove.forEach(id => store.delete(id));
    tx.oncomplete = () => {
      Object.keys(podcastPlaylists).forEach(name => {
        podcastPlaylists[name] = podcastPlaylists[name].filter(id => !idsToRemove.includes(id));
      });
      savePodcastPlaylists();
      const txPos = podcastDB.transaction("positions", "readwrite");
      const posStore = txPos.objectStore("positions");
      idsToRemove.forEach(id => {
        delete podcastPositions[id];
        posStore.delete(id);
      });
      podcastRecent = podcastRecent.filter(e => !idsToRemove.includes(e.id));
      savePodcastRecent();
      renderPodcastRecent();
      if (currentPodcastId !== null && idsToRemove.includes(currentPodcastId)) {
        currentPodcastId = null;
        currentPodcastDisplay.textContent = "No podcast selected";
        podcastPlayer.pause();
        podcastPlayer.removeAttribute("src");
        playPausePodcastBtn.textContent = "Play";
      }
      loadPodcastsFromDB();
      renderPodcastPlaylistSongs();
      renderPodcastPlaylists();
      refreshHistoryCache();
      renderPodcastHistory();
      if (userAccount) userAccount.updateAccountInfo();
    };
    tx.onerror = () => {
      console.error("Failed to delete selected podcasts", tx.error);
      alert("Could not delete the selected podcasts.");
    };
  });
}

playPausePodcastBtn.addEventListener("click", () => {
  if (!currentPodcastId && podcasts.length) return playPodcastById(podcasts[0].id);
  if (podcastPlayer.paused) {
    podcastPlayer.play();
    playPausePodcastBtn.textContent = "Pause";
  } else {
    podcastPlayer.pause();
    playPausePodcastBtn.textContent = "Play";
  }
});

nextPodcastBtn.addEventListener("click", () => {
  podcastPlaylistPlaying = podcastPlaylistPlaying && !!currentPodcastPlaylist;
  playNextPodcast();
});

prevPodcastBtn.addEventListener("click", () => playPrevPodcast());

toggleRepeatPodcastBtn.addEventListener("click", () => {
  podcastRepeat = !podcastRepeat;
  podcastPlayer.loop = podcastRepeat;
  toggleRepeatPodcastBtn.textContent = `Repeat: ${podcastRepeat ? "On" : "Off"}`;
});

podcastPlayer.addEventListener("timeupdate", () => {
  if (!podcastPlayer.duration) return;
  podcastProgress.value = podcastPlayer.currentTime / podcastPlayer.duration * 100;
  updateRangeFill(podcastProgress);
  podcastCurrentTimeEl.textContent = formatTime(podcastPlayer.currentTime);
  podcastDurationEl.textContent = formatTime(podcastPlayer.duration);
  if (currentPodcastId !== null) {
    const now = Date.now();
    if (now - lastPodcastPositionSave > POSITION_SAVE_INTERVAL) {
      lastPodcastPositionSave = now;
      savePodcastPosition(currentPodcastId, podcastPlayer.currentTime);
    }
  }
});

podcastProgress.addEventListener("input", () => {
  if (podcastPlayer.duration) podcastPlayer.currentTime = podcastProgress.value / 100 * podcastPlayer.duration;
  updateRangeFill(podcastProgress);
});

podcastPlayer.addEventListener("pause", () => {
  if (currentPodcastId !== null && podcastPlayer.duration) {
    savePodcastPosition(currentPodcastId, podcastPlayer.currentTime);
  }
});

podcastPlayer.addEventListener("ended", () => {
  if (currentPodcastId !== null) {
    deletePodcastPosition(currentPodcastId);
  }
  playNextPodcast();
});

document.getElementById("forward-10-podcast").addEventListener("click", () => {
  podcastPlayer.currentTime += 10;
});

document.getElementById("rewind-10-podcast").addEventListener("click", () => {
  podcastPlayer.currentTime = Math.max(0, podcastPlayer.currentTime - 10);
});

(function addPodcastLoopPlaylistButton() {
  const controls = document.querySelector("#podcast-page .player-container .controls");
  if (!controls) return;
  const btn = document.createElement("button");
  btn.className = "action-button";
  btn.textContent = "🔁 Loop Playlist: Off";
  controls.insertBefore(btn, controls.firstChild);
  btn.addEventListener("click", () => {
    podcastLoopPlaylist = !podcastLoopPlaylist;
    btn.textContent = `🔁 Loop Playlist: ${podcastLoopPlaylist ? "On" : "Off"}`;
  });
})();

let podcastPlaylistMeta = {};

let podcastPlaylistSortMode = "name";

function podcastPlaylistCtx() {
  return {
    playlistsObj: podcastPlaylists,
    metaObj: podcastPlaylistMeta,
    mediaArray: () => podcasts,
    historyType: "podcast",
    listEl: podcastPlaylistsEl,
    toolbarEl: podcastPlaylistToolbarEl,
    tracksEl: playlistPodcastSongs,
    headerEl: podcastPlaylistHeaderEl,
    titleEl: podcastPlaylistTitle,
    getCurrent: () => currentPodcastPlaylist,
    setCurrent: v => {
      currentPodcastPlaylist = v;
    },
    getSortMode: () => podcastPlaylistSortMode,
    setSortMode: v => {
      podcastPlaylistSortMode = v;
      appSet("podcastPlaylistSortMode", v);
    },
    saveFn: savePodcastPlaylists,
    saveMetaFn: savePodcastPlaylistMeta,
    renderNamesFn: renderPodcastPlaylists,
    renderTracksFn: renderPodcastPlaylistSongs,
    selectFn: selectPodcastPlaylist,
    playByIdFn: id => playPodcastById(id),
    currentPlayingId: () => currentPodcastId,
    setPlaying: v => {
      podcastPlaylistPlaying = v;
    }
  };
}

function renderPodcastPlaylists() {
  renderPlaylistNamesGeneric(podcastPlaylistCtx());
}

function selectPodcastPlaylist(name) {
  currentPodcastPlaylist = name;
  podcastPlaylistTitle.textContent = isSmartPlaylist(name) ? smartPlaylistLabel(name) : name;
  renderPodcastPlaylistSongs();
  renderPodcastPlaylists();
}

function renderPodcastPlaylistSongs() {
  renderPlaylistTracksGeneric(podcastPlaylistCtx());
}

function savePodcastPlaylists() {
  if (!podcastDB || !currentUserId) return;
  const tx = podcastDB.transaction("playlists", "readwrite");
  const store = tx.objectStore("playlists");
  const clearReq = store.getAll();
  clearReq.onsuccess = () => {
    clearReq.result.filter(item => item.userId === currentUserId).forEach(item => store.delete(item.name));
    Object.keys(podcastPlaylists).forEach(name => {
      store.put({
        name: name,
        songs: podcastPlaylists[name],
        userId: currentUserId
      });
    });
  };
}

function savePodcastPlaylistMeta() {
  appSet("podcastPlaylistMeta", podcastPlaylistMeta);
}

document.getElementById("btn-create-podcast-playlist").addEventListener("click", () => {
  const name = podcastPlaylistName.value.trim();
  if (!name || podcastPlaylists[name] || isSmartPlaylist(name)) return alert("Invalid or duplicate playlist name");
  podcastPlaylists[name] = [];
  getPlaylistMeta(podcastPlaylistMeta, name);
  podcastPlaylistName.value = "";
  renderPodcastPlaylists();
  savePodcastPlaylists();
  savePodcastPlaylistMeta();
});

document.getElementById("btn-delete-podcast-playlist").addEventListener("click", () => {
  if (!currentPodcastPlaylist || isSmartPlaylist(currentPodcastPlaylist)) return alert("Select a playlist first");
  delete podcastPlaylists[currentPodcastPlaylist];
  delete podcastPlaylistMeta[currentPodcastPlaylist];
  currentPodcastPlaylist = null;
  podcastPlaylistTitle.textContent = "Select a playlist";
  renderPodcastPlaylistSongs();
  renderPodcastPlaylists();
  savePodcastPlaylists();
  savePodcastPlaylistMeta();
});

document.getElementById("btn-add-selected-to-podcast-playlist").addEventListener("click", () => {
  if (!currentPodcastPlaylist || isSmartPlaylist(currentPodcastPlaylist)) return alert("Select a playlist first");
  document.querySelectorAll("#podcast-list input[type=checkbox]:checked").forEach(cb => {
    const id = Number(cb.dataset.id);
    if (!podcastPlaylists[currentPodcastPlaylist].includes(id)) podcastPlaylists[currentPodcastPlaylist].push(id);
  });
  touchPlaylistMeta(podcastPlaylistMeta, currentPodcastPlaylist);
  renderPodcastPlaylistSongs();
  renderPodcastPlaylists();
  savePodcastPlaylists();
  savePodcastPlaylistMeta();
});

document.getElementById("btn-add-all-to-podcast-playlist").addEventListener("click", () => {
  if (!currentPodcastPlaylist || isSmartPlaylist(currentPodcastPlaylist)) return alert("Select a playlist first");
  podcasts.forEach(episode => {
    if (!podcastPlaylists[currentPodcastPlaylist].includes(episode.id)) podcastPlaylists[currentPodcastPlaylist].push(episode.id);
  });
  touchPlaylistMeta(podcastPlaylistMeta, currentPodcastPlaylist);
  renderPodcastPlaylistSongs();
  renderPodcastPlaylists();
  savePodcastPlaylists();
  savePodcastPlaylistMeta();
});

document.getElementById("btn-remove-from-podcast-playlist").addEventListener("click", () => {
  if (!currentPodcastPlaylist || isSmartPlaylist(currentPodcastPlaylist)) return;
  const toRemove = Array.from(playlistPodcastSongs.querySelectorAll("input[type=checkbox]:checked")).map(cb => Number(cb.dataset.id));
  podcastPlaylists[currentPodcastPlaylist] = podcastPlaylists[currentPodcastPlaylist].filter(id => !toRemove.includes(id));
  touchPlaylistMeta(podcastPlaylistMeta, currentPodcastPlaylist);
  renderPodcastPlaylistSongs();
  renderPodcastPlaylists();
  savePodcastPlaylists();
  savePodcastPlaylistMeta();
});

document.getElementById("btn-clear-podcast-playlist").addEventListener("click", () => {
  if (!currentPodcastPlaylist || isSmartPlaylist(currentPodcastPlaylist)) return;
  podcastPlaylists[currentPodcastPlaylist] = [];
  touchPlaylistMeta(podcastPlaylistMeta, currentPodcastPlaylist);
  renderPodcastPlaylistSongs();
  renderPodcastPlaylists();
  savePodcastPlaylists();
  savePodcastPlaylistMeta();
});

document.getElementById("btn-play-podcast-playlist").addEventListener("click", () => {
  const ids = getActivePlaylistIds(podcastPlaylistCtx());
  if (!currentPodcastPlaylist || !ids.length) {
    return alert("Select a playlist with episodes");
  }
  podcastPlaylistPlaying = true;
  playPodcastById(ids[0]);
});

(function enablePodcastPlaylistPanelDrop() {
  const wrap = document.getElementById("podcast-playlist-wrap");
  if (!wrap) return;
  wrap.addEventListener("dragover", e => {
    if (!currentPodcastPlaylist || !e.dataTransfer.types.includes("text/plain")) return;
    e.preventDefault();
    e.dataTransfer.dropEffect = "copy";
    wrap.classList.add("drag-over");
  });
  wrap.addEventListener("dragleave", e => {
    if (!wrap.contains(e.relatedTarget)) wrap.classList.remove("drag-over");
  });
  wrap.addEventListener("drop", e => {
    e.preventDefault();
    wrap.classList.remove("drag-over");
    const name = currentPodcastPlaylist;
    if (!name) return;
    const id = Number(e.dataTransfer.getData("text/plain"));
    if (!id || !podcasts.find(p => p.id === id)) return;
    if (!podcastPlaylists[name].includes(id)) podcastPlaylists[name].push(id);
    savePodcastPlaylists();
    renderPodcastPlaylistSongs();
    renderPodcastPlaylists();
  });
})();

function setupPodcastDragReorder() {
  let draggedLi = null;
  const list = document.getElementById("podcast-playlist-songs");
  if (!list) return;
  list.addEventListener("dragstart", e => {
    draggedLi = e.target.closest("li");
    if (!draggedLi) return;
    draggedLi.classList.add("dragging");
    e.dataTransfer.effectAllowed = "move";
  });
  list.addEventListener("dragend", () => {
    if (draggedLi) draggedLi.classList.remove("dragging");
    draggedLi = null;
    list.querySelectorAll("li").forEach(li => li.removeAttribute("draggable"));
    const newOrder = Array.from(list.children).map(li => Number(li.dataset.id));
    if (currentPodcastPlaylist) {
      podcastPlaylists[currentPodcastPlaylist] = newOrder;
      savePodcastPlaylists();
    }
  });
  list.addEventListener("dragover", e => {
    e.preventDefault();
    if (!draggedLi) return;
    const afterElement = getDragAfterElement(list, e.clientY);
    if (afterElement == null) list.appendChild(draggedLi); else list.insertBefore(draggedLi, afterElement);
  });
  function getDragAfterElement(container, y) {
    const els = [ ...container.querySelectorAll("li:not(.dragging)") ];
    return els.reduce((closest, child) => {
      const box = child.getBoundingClientRect();
      const offset = y - box.top - box.height / 2;
      if (offset < 0 && offset > closest.offset) return {
        offset: offset,
        element: child
      };
      return closest;
    }, {
      offset: Number.NEGATIVE_INFINITY
    }).element;
  }
}

setupPodcastDragReorder();

if (exportPodcastPlaylistBtn) {
  exportPodcastPlaylistBtn.addEventListener("click", () => {
    exportPlaylistFile(currentPodcastPlaylist, currentPodcastPlaylist ? getActivePlaylistIds(podcastPlaylistCtx()) : null, podcasts);
  });
}

PLAYLIST_FOLDER_IMPORT_HANDLERS["podcast-playlist-import"] = async (files, folderName) => {
  await importPlaylistFolder(files, folderName, podcastDB, "episodes", podcasts, podcastPlaylists, savePodcastPlaylists, renderPodcastPlaylistSongs, renderPodcastPlaylists, selectPodcastPlaylist, podcastPlaylistMeta, savePodcastPlaylistMeta, "audio");
  renderPodcasts(podcastSearch.value);
};

if (podcastPlaylistImportInput) {
  podcastPlaylistImportInput.addEventListener("change", async e => {
    const file = e.target.files[0];
    if (!file) return;
    try {
      await importPlaylistFile(file, podcastDB, "episodes", podcasts, podcastPlaylists, savePodcastPlaylists, renderPodcastPlaylistSongs, renderPodcastPlaylists, selectPodcastPlaylist, podcastPlaylistMeta, savePodcastPlaylistMeta, "audio");
    } finally {
      e.target.value = "";
    }
    renderPodcasts(podcastSearch.value);
  });
}

document.addEventListener("keydown", e => {
  if (e.target.tagName === "INPUT" || e.target.tagName === "TEXTAREA") return;
  if (e.code === "Space") {
    e.preventDefault();
    if (pages.music.classList.contains("active")) playPauseBtn.click(); else if (pages.video.classList.contains("active")) playPauseVideoBtn.click(); else if (pages.podcast.classList.contains("active")) playPausePodcastBtn.click();
  }
  if (e.key && e.key.toLowerCase() === "m" && !e.ctrlKey && !e.shiftKey && !e.altKey && !e.metaKey) {
    e.preventDefault();
    if (pages.music.classList.contains("active")) musicMuteBtn.click(); else if (pages.video.classList.contains("active")) videoMuteBtn.click(); else if (pages.podcast.classList.contains("active")) podcastMuteBtn.click();
  }
  if (e.code === "ArrowRight" && e.shiftKey) {
    e.preventDefault();
    if (pages.music.classList.contains("active")) document.getElementById("forward-10")?.click(); else if (pages.video.classList.contains("active")) document.getElementById("forward-10-video")?.click(); else if (pages.podcast.classList.contains("active")) document.getElementById("forward-10-podcast")?.click();
  }
  if (e.code === "ArrowLeft" && e.shiftKey) {
    e.preventDefault();
    if (pages.music.classList.contains("active")) document.getElementById("rewind-10")?.click(); else if (pages.video.classList.contains("active")) document.getElementById("rewind-10-video")?.click(); else if (pages.podcast.classList.contains("active")) document.getElementById("rewind-10-podcast")?.click();
  }
  if (e.code === "ArrowRight" && !e.shiftKey && e.ctrlKey) {
    e.preventDefault();
    if (pages.music.classList.contains("active")) nextBtn?.click(); else if (pages.video.classList.contains("active")) nextVideoBtn?.click(); else if (pages.podcast.classList.contains("active")) nextPodcastBtn?.click();
  }
  if (e.code === "ArrowLeft" && !e.shiftKey && e.ctrlKey) {
    e.preventDefault();
    if (pages.music.classList.contains("active")) prevBtn?.click(); else if (pages.video.classList.contains("active")) prevVideoBtn?.click(); else if (pages.podcast.classList.contains("active")) prevPodcastBtn?.click();
  }
});

(function() {
  const musicMini = document.getElementById("music-mini-player");
  const musicMiniToggleBtn = document.getElementById("music-mini-player-toggle");
  const musicMiniClose = document.getElementById("mp-music-close");
  const musicMiniTitle = document.getElementById("mp-music-title");
  const musicMiniSource = document.getElementById("mp-music-source");
  const musicMiniProgress = document.getElementById("mp-music-progress");
  const musicMiniPlay = document.getElementById("mp-music-play");
  const musicMiniPrev = document.getElementById("mp-music-prev");
  const musicMiniNext = document.getElementById("mp-music-next");
  const musicMiniRewind = document.getElementById("mp-music-rewind");
  const musicMiniForward = document.getElementById("mp-music-forward");
  const musicMiniArt = document.getElementById("mp-music-art");
  const musicMiniHandle = musicMini.querySelector(".mini-player-drag-handle");
  const videoMini = document.getElementById("video-mini-player");
  const videoMiniToggleBtn = document.getElementById("video-mini-player-toggle");
  const videoMiniClose = document.getElementById("mp-video-close");
  const videoMiniTitle = document.getElementById("mp-video-title");
  const videoMiniSource = document.getElementById("mp-video-source");
  const videoMiniProgress = document.getElementById("mp-video-progress");
  const videoMiniPlay = document.getElementById("mp-video-play");
  const videoMiniPrev = document.getElementById("mp-video-prev");
  const videoMiniNext = document.getElementById("mp-video-next");
  const videoMiniRewind = document.getElementById("mp-video-rewind");
  const videoMiniForward = document.getElementById("mp-video-forward");
  const videoMiniThumb = document.getElementById("mp-video-thumb");
  const videoMiniHandle = videoMini.querySelector(".mini-player-drag-handle");
  const podcastMini = document.getElementById("podcast-mini-player");
  const podcastMiniToggleBtn = document.getElementById("podcast-mini-player-toggle");
  const podcastMiniClose = document.getElementById("mp-podcast-close");
  const podcastMiniTitle = document.getElementById("mp-podcast-title");
  const podcastMiniSource = document.getElementById("mp-podcast-source");
  const podcastMiniProgress = document.getElementById("mp-podcast-progress");
  const podcastMiniPlay = document.getElementById("mp-podcast-play");
  const podcastMiniPrev = document.getElementById("mp-podcast-prev");
  const podcastMiniNext = document.getElementById("mp-podcast-next");
  const podcastMiniRewind = document.getElementById("mp-podcast-rewind");
  const podcastMiniForward = document.getElementById("mp-podcast-forward");
  const podcastMiniArt = document.getElementById("mp-podcast-art");
  const podcastMiniHandle = podcastMini.querySelector(".mini-player-drag-handle");
  const videoMiniPlaceholder = document.createElement("div");
  videoMiniPlaceholder.className = "mini-player-thumb-placeholder";
  videoMiniPlaceholder.textContent = "🎬";
  videoMiniPlaceholder.style.display = "none";
  videoMiniThumb.appendChild(videoMiniPlaceholder);
  const musicHome = musicMini.parentElement;
  const videoHome = videoMini.parentElement;
  const podcastHome = podcastMini.parentElement;
  let musicMiniOn = false;
  let videoMiniOn = false;
  let podcastMiniOn = false;
  let musicPipWindow = null;
  let videoPipWindow = null;
  let podcastPipWindow = null;
  function otherMiniOff(exceptKey) {
    if (exceptKey !== "music" && musicMiniOn) setMusicMiniState(false);
    if (exceptKey !== "video" && videoMiniOn) setVideoMiniState(false);
    if (exceptKey !== "podcast" && podcastMiniOn) setPodcastMiniState(false);
    turnOffOtherMinis(exceptKey);
  }
  registerMiniPlayer("music", () => setMusicMiniState(false), () => musicMiniOn);
  registerMiniPlayer("video", () => setVideoMiniState(false), () => videoMiniOn);
  registerMiniPlayer("podcast", () => setPodcastMiniState(false), () => podcastMiniOn);
  async function setMusicMiniState(on) {
    musicMiniOn = on;
    musicMiniToggleBtn.classList.toggle("active-toggle", on);
    if (on) {
      if (supportsDocPip) {
        try {
          musicPipWindow = await openDocPip(musicMini, musicHome, () => {
            musicMiniOn = false;
            musicMini.classList.remove("show");
            musicMiniToggleBtn.classList.remove("active-toggle");
            musicPipWindow = null;
          }, 320, 240);
          return;
        } catch (err) {
          console.error("Document Picture-in-Picture failed, falling back to floating panel", err);
        }
      }
      musicMini.classList.add("show");
    } else {
      if (musicPipWindow) {
        musicPipWindow.close();
        musicPipWindow = null;
      }
      musicMini.classList.remove("show");
    }
  }
  function moveVideoElement(container, mini) {
    container.appendChild(videoPlayer);
    videoPlayer.classList.toggle("video-player--mini", mini);
    const showPlaceholder = mini && currentVideoId === null;
    videoPlayer.style.display = showPlaceholder ? "none" : "";
    videoMiniPlaceholder.style.display = showPlaceholder ? "" : "none";
  }
  async function setVideoMiniState(on) {
    videoMiniOn = on;
    videoMiniToggleBtn.classList.toggle("active-toggle", on);
    if (on) {
      moveVideoElement(videoMiniThumb, true);
      if (supportsDocPip) {
        try {
          videoPipWindow = await openDocPip(videoMini, videoHome, () => {
            videoMiniOn = false;
            videoMini.classList.remove("show");
            videoMiniToggleBtn.classList.remove("active-toggle");
            videoPipWindow = null;
            moveVideoElement(videoDock, false);
          }, 360, 460);
          return;
        } catch (err) {
          console.error("Document Picture-in-Picture failed, falling back to floating panel", err);
        }
      }
      videoMini.classList.add("show");
    } else {
      if (videoPipWindow) {
        videoPipWindow.close();
        videoPipWindow = null;
      }
      videoMini.classList.remove("show");
      moveVideoElement(videoDock, false);
    }
  }
  async function setPodcastMiniState(on) {
    podcastMiniOn = on;
    podcastMiniToggleBtn.classList.toggle("active-toggle", on);
    if (on) {
      if (supportsDocPip) {
        try {
          podcastPipWindow = await openDocPip(podcastMini, podcastHome, () => {
            podcastMiniOn = false;
            podcastMini.classList.remove("show");
            podcastMiniToggleBtn.classList.remove("active-toggle");
            podcastPipWindow = null;
          }, 320, 240);
          return;
        } catch (err) {
          console.error("Document Picture-in-Picture failed, falling back to floating panel", err);
        }
      }
      podcastMini.classList.add("show");
    } else {
      if (podcastPipWindow) {
        podcastPipWindow.close();
        podcastPipWindow = null;
      }
      podcastMini.classList.remove("show");
    }
  }
  musicMiniToggleBtn.addEventListener("click", () => {
    const turningOn = !musicMiniOn;
    if (turningOn) otherMiniOff("music");
    setMusicMiniState(turningOn);
  });
  musicMiniClose.addEventListener("click", () => setMusicMiniState(false));
  videoMiniToggleBtn.addEventListener("click", () => {
    const turningOn = !videoMiniOn;
    if (turningOn) otherMiniOff("video");
    setVideoMiniState(turningOn);
  });
  videoMiniClose.addEventListener("click", () => setVideoMiniState(false));
  podcastMiniToggleBtn.addEventListener("click", () => {
    const turningOn = !podcastMiniOn;
    if (turningOn) otherMiniOff("podcast");
    setPodcastMiniState(turningOn);
  });
  podcastMiniClose.addEventListener("click", () => setPodcastMiniState(false));
  function activeTerminal() {
    if (pages.music.classList.contains("active")) return "music";
    if (pages.video.classList.contains("active")) return "video";
    if (pages.podcast.classList.contains("active")) return "podcast";
    return null;
  }
  onPageChange = name => {
    if (name === "music" && musicMiniOn) setMusicMiniState(false);
    if (name === "video" && videoMiniOn) setVideoMiniState(false);
    if (name === "podcast" && podcastMiniOn) setPodcastMiniState(false);
  };
  audioPlayer.addEventListener("play", () => {
    musicMiniPlay.textContent = "⏸︎";
    musicMiniArt.classList.add("spinning");
  });
  audioPlayer.addEventListener("pause", () => {
    musicMiniPlay.textContent = "▶︎";
    musicMiniArt.classList.remove("spinning");
  });
  videoPlayer.addEventListener("play", () => {
    videoMiniPlay.textContent = "⏸︎";
  });
  videoPlayer.addEventListener("pause", () => {
    videoMiniPlay.textContent = "▶︎";
  });
  podcastPlayer.addEventListener("play", () => {
    podcastMiniPlay.textContent = "⏸︎";
  });
  podcastPlayer.addEventListener("pause", () => {
    podcastMiniPlay.textContent = "▶︎";
  });
  musicMiniPlay.addEventListener("click", () => playPauseBtn.click());
  musicMiniPrev.addEventListener("click", () => prevBtn.click());
  musicMiniNext.addEventListener("click", () => nextBtn.click());
  musicMiniRewind.addEventListener("click", () => document.getElementById("rewind-10")?.click());
  musicMiniForward.addEventListener("click", () => document.getElementById("forward-10")?.click());
  videoMiniPlay.addEventListener("click", () => playPauseVideoBtn.click());
  videoMiniPrev.addEventListener("click", () => prevVideoBtn.click());
  videoMiniNext.addEventListener("click", () => nextVideoBtn.click());
  videoMiniRewind.addEventListener("click", () => document.getElementById("rewind-10-video")?.click());
  videoMiniForward.addEventListener("click", () => document.getElementById("forward-10-video")?.click());
  podcastMiniPlay.addEventListener("click", () => playPausePodcastBtn.click());
  podcastMiniPrev.addEventListener("click", () => prevPodcastBtn.click());
  podcastMiniNext.addEventListener("click", () => nextPodcastBtn.click());
  podcastMiniRewind.addEventListener("click", () => document.getElementById("rewind-10-podcast")?.click());
  podcastMiniForward.addEventListener("click", () => document.getElementById("forward-10-podcast")?.click());
  musicMiniProgress.addEventListener("input", () => {
    if (audioPlayer.duration) audioPlayer.currentTime = musicMiniProgress.value / 100 * audioPlayer.duration;
    updateRangeFill(musicMiniProgress);
  });
  videoMiniProgress.addEventListener("input", () => {
    if (videoPlayer.duration) videoPlayer.currentTime = videoMiniProgress.value / 100 * videoPlayer.duration;
    updateRangeFill(videoMiniProgress);
  });
  podcastMiniProgress.addEventListener("input", () => {
    if (podcastPlayer.duration) podcastPlayer.currentTime = podcastMiniProgress.value / 100 * podcastPlayer.duration;
    updateRangeFill(podcastMiniProgress);
  });
  audioPlayer.addEventListener("timeupdate", () => {
    if (!audioPlayer.duration) return;
    musicMiniProgress.value = audioPlayer.currentTime / audioPlayer.duration * 100;
    updateRangeFill(musicMiniProgress);
  });
  videoPlayer.addEventListener("timeupdate", () => {
    if (!videoPlayer.duration) return;
    videoMiniProgress.value = videoPlayer.currentTime / videoPlayer.duration * 100;
    updateRangeFill(videoMiniProgress);
  });
  podcastPlayer.addEventListener("timeupdate", () => {
    if (!podcastPlayer.duration) return;
    podcastMiniProgress.value = podcastPlayer.currentTime / podcastPlayer.duration * 100;
    updateRangeFill(podcastMiniProgress);
  });
  new MutationObserver(() => {
    musicMiniTitle.textContent = currentMusicDisplay.textContent;
    musicMiniSource.textContent = currentMusicId !== null ? currentMusicSource() : "";
  }).observe(currentMusicDisplay, {
    childList: true,
    characterData: true,
    subtree: true
  });
  new MutationObserver(() => {
    videoMiniTitle.textContent = videoCurrentDisplay.textContent;
    videoMiniSource.textContent = currentVideoId !== null ? currentVideoSource() : "";
  }).observe(videoCurrentDisplay, {
    childList: true,
    characterData: true,
    subtree: true
  });
  new MutationObserver(() => {
    podcastMiniTitle.textContent = currentPodcastDisplay.textContent;
    podcastMiniSource.textContent = currentPodcastId !== null ? currentPodcastSource() : "";
  }).observe(currentPodcastDisplay, {
    childList: true,
    characterData: true,
    subtree: true
  });
  function makeDraggable(panel, handle) {
    let offsetX = 0, offsetY = 0, dragging = false;
    handle.addEventListener("mousedown", e => {
      if (panel.ownerDocument !== document) return;
      dragging = true;
      panel.classList.add("dragging");
      const rect = panel.getBoundingClientRect();
      offsetX = e.clientX - rect.left;
      offsetY = e.clientY - rect.top;
      panel.style.right = "auto";
      panel.style.bottom = "auto";
      panel.style.left = `${rect.left}px`;
      panel.style.top = `${rect.top}px`;
    });
    window.addEventListener("mousemove", e => {
      if (!dragging) return;
      panel.style.left = `${e.clientX - offsetX}px`;
      panel.style.top = `${e.clientY - offsetY}px`;
    });
    window.addEventListener("mouseup", () => {
      dragging = false;
      panel.classList.remove("dragging");
    });
  }
  makeDraggable(musicMini, musicMiniHandle);
  makeDraggable(videoMini, videoMiniHandle);
  makeDraggable(podcastMini, podcastMiniHandle);
})();

function getAllUserMedia(db, storeName) {
  return new Promise(resolve => {
    if (!db || !currentUserId) return resolve([]);
    const tx = db.transaction(storeName, "readonly");
    const store = tx.objectStore(storeName);
    const request = store.getAll();
    request.onsuccess = () => resolve(request.result.filter(item => item.userId === currentUserId));
    request.onerror = () => resolve([]);
  });
}

function replaceUserMedia(db, storeName, items) {
  return new Promise(resolve => {
    if (!db || !currentUserId) return resolve(new Map);
    const tx = db.transaction(storeName, "readwrite");
    const store = tx.objectStore(storeName);
    const idMap = new Map;
    const getAllReq = store.getAll();
    getAllReq.onsuccess = () => {
      getAllReq.result.filter(item => item.userId === currentUserId).forEach(item => store.delete(item.id));
      items.forEach(item => {
        const {id: id, oldId: oldId, ...rest} = item;
        const addReq = store.add({
          ...rest,
          userId: currentUserId
        });
        addReq.onsuccess = () => {
          if (oldId !== undefined) idMap.set(oldId, addReq.result);
        };
      });
    };
    tx.oncomplete = () => resolve(idMap);
    tx.onerror = () => resolve(idMap);
  });
}

function deleteMediaForUser(db, storeName, userId) {
  return new Promise(resolve => {
    if (!db) return resolve();
    const tx = db.transaction(storeName, "readwrite");
    const store = tx.objectStore(storeName);
    const getAllReq = store.getAll();
    getAllReq.onsuccess = () => {
      getAllReq.result.filter(item => item.userId === userId).forEach(item => {
        const key = storeName === "playlists" ? item.name : item.id;
        store.delete(key);
      });
    };
    tx.oncomplete = () => resolve();
    tx.onerror = () => resolve();
  });
}

async function deleteAllMediaForUser(userId) {
  await Promise.all([ deleteMediaForUser(musicDB, "music", userId), deleteMediaForUser(videoDB, "videos", userId), deleteMediaForUser(podcastDB, "episodes", userId), deleteMediaForUser(podcastDB, "playlists", userId), deleteMediaForUser(podcastDB, "positions", userId) ]);
  await new Promise(resolve => {
    openHistoryStore().then(db => {
      const tx = db.transaction("kv", "readwrite");
      tx.objectStore("kv").delete(`sqlite_data_u${userId}`);
      tx.oncomplete = () => resolve();
      tx.onerror = () => resolve();
    }).catch(() => resolve());
  });
}

function resumeLastPlayedMusic() {
  const id = appGet("lastMusicId", null);
  if (id === null || id === undefined) return;
  const song = music.find(s => s.id === id);
  if (!song) return;
  playMusicById(id, true);
}

function resumeLastPlayedVideo() {
  const id = appGet("lastVideoId", null);
  if (id === null || id === undefined) return;
  const video = videos.find(v => v.id === id);
  if (!video) return;
  playVideoById(id, true);
}

function resumeLastPlayedPodcast() {
  const id = appGet("lastPodcastId", null);
  if (id === null || id === undefined) return;
  const episode = podcasts.find(e => e.id === id);
  if (!episode) return;
  playPodcastById(id, true);
}

function resetAllMediaState() {
  music.length = 0;
  videos.length = 0;
  documentary.length = 0;
  movie.length = 0;
  comedy.length = 0;
  webseries.length = 0;
  podcasts.length = 0;
  games.length = 0;
  books.length = 0;
  bookmarks.length = 0;
  playlists = {};
  videoPlaylists = {};
  podcastPlaylists = {};
  documentaryPlaylists = {};
  moviePlaylists = {};
  comedyPlaylists = {};
  webseriesPlaylists = {};
  gamesPlaylists = {};
  booksPlaylists = {};
  musicPlaylistMeta = {};
  videoPlaylistMeta = {};
  podcastPlaylistMeta = {};
  documentaryPlaylistMeta = {};
  moviePlaylistMeta = {};
  comedyPlaylistMeta = {};
  webseriesPlaylistMeta = {};
  gamesPlaylistMeta = {};
  booksPlaylistMeta = {};
  currentPlaylist = null;
  currentVideoPlaylist = null;
  currentPodcastPlaylist = null;
  currentDocumentaryPlaylist = null;
  currentMoviePlaylist = null;
  currentComedyPlaylist = null;
  currentWebSeriesPlaylist = null;
  currentGamesPlaylist = null;
  currentBooksPlaylist = null;
  currentMusicId = null;
  currentVideoId = null;
  currentDocumentaryId = null;
  currentMovieId = null;
  currentComedyId = null;
  currentWebSeriesId = null;
  currentPodcastId = null;
  currentGameId = null;
  currentBookId = null;
  musicPositions = {};
  videoPositions = {};
  documentaryPositions = {};
  moviePositions = {};
  comedyPositions = {};
  webseriesPositions = {};
  podcastPositions = {};
  musicRecent = [];
  videoRecent = [];
  podcastRecent = [];
  bookmarkRecent = [];
  bookmarkCollections = {};
  currentBookmarkCollection = null;
  selectedBookmarkId = null;
  Object.keys(QUEUE_TYPES).forEach(type => {
    mediaQueues[type] = [];
    renderQueue(type);
  });
  audioPlayer.pause();
  audioPlayer.removeAttribute("src");
  if (audioPlayer.dataset.url) {
    URL.revokeObjectURL(audioPlayer.dataset.url);
    delete audioPlayer.dataset.url;
  }
  currentMusicDisplay.textContent = "No music selected";
  playPauseBtn.textContent = "Play";
  videoPlayer.pause();
  videoPlayer.removeAttribute("src");
  if (videoPlayer.dataset.url) {
    URL.revokeObjectURL(videoPlayer.dataset.url);
    delete videoPlayer.dataset.url;
  }
  videoCurrentDisplay.textContent = "No video selected";
  playPauseVideoBtn.textContent = "Play";
  stopDocumentary();
  stopMovie();
  stopComedy();
  stopWebSeries();
  podcastPlayer.pause();
  podcastPlayer.removeAttribute("src");
  if (podcastPlayer.dataset.url) {
    URL.revokeObjectURL(podcastPlayer.dataset.url);
    delete podcastPlayer.dataset.url;
  }
  currentPodcastDisplay.textContent = "No podcast selected";
  playPausePodcastBtn.textContent = "Play";
  if (gameFrame.dataset.url) {
    URL.revokeObjectURL(gameFrame.dataset.url);
    delete gameFrame.dataset.url;
  }
  gameFrame.removeAttribute("src");
  currentGameDisplay.textContent = "No game selected";
  if (bookFrame.dataset.url) {
    URL.revokeObjectURL(bookFrame.dataset.url);
    delete bookFrame.dataset.url;
  }
  bookFrame.removeAttribute("src");
  currentBookDisplay.textContent = "No book selected";
  renderMusic("");
  renderVideos("");
  renderDocumentary("");
  renderMovie("");
  renderComedy("");
  renderWebSeries("");
  renderPodcasts("");
  renderGames("");
  renderBooks("");
  renderBookmarks("");
  renderBookmarkCollections();
  renderCollectionBookmarks();
  renderBookmarkRecent();
  renderBookmarkPreview();
  bookmarkCollectionTitle.textContent = "Select a collection";
  renderPlaylists();
  renderVideoPlaylists();
  renderPodcastPlaylists();
  renderDocumentaryPlaylists();
  renderMoviePlaylists();
  renderComedyPlaylists();
  renderWebSeriesPlaylists();
  renderGamesPlaylists();
  renderBooksPlaylists();
  renderMusicRecent();
  renderVideoRecent();
  renderPodcastRecent();
  playlistTitle.textContent = "Select a playlist";
  videoPlaylistTitle.textContent = "Select a playlist";
  podcastPlaylistTitle.textContent = "Select a playlist";
  documentaryPlaylistTitle.textContent = "Select a playlist";
  moviePlaylistTitle.textContent = "Select a playlist";
  comedyPlaylistTitle.textContent = "Select a playlist";
  webseriesPlaylistTitle.textContent = "Select a playlist";
  gamesPlaylistTitle.textContent = "Select a playlist";
  booksPlaylistTitle.textContent = "Select a playlist";
  renderPlaylistMusic();
  renderPlaylistVideos();
  renderPodcastPlaylistSongs();
  renderPlaylistDocumentary();
  renderPlaylistMovie();
  renderPlaylistComedy();
  renderPlaylistWebSeries();
  renderPlaylistGames();
  renderPlaylistBooks();
  historyData = null;
  historyReady = false;
  historyCache.clear();
  renderMusicHistory();
  renderVideoHistory();
  renderPodcastHistory();
  renderBookmarkHistory();
  refreshVolumeControlFromStorage(musicVolume, "musicVolume", () => {
    const v = Number(musicVolume.value);
    audioPlayer.volume = v / 100;
    audioPlayer.muted = v === 0;
    musicVolumeLabel.textContent = `${v}%`;
    musicMuteBtn.textContent = volumeIconFor(v, audioPlayer.muted);
    updateRangeFill(musicVolume);
  });
  refreshVolumeControlFromStorage(videoVolume, "videoVolume", () => {
    const v = Number(videoVolume.value);
    videoPlayer.volume = v / 100;
    videoPlayer.muted = v === 0;
    videoVolumeLabel.textContent = `${v}%`;
    videoMuteBtn.textContent = volumeIconFor(v, videoPlayer.muted);
    updateRangeFill(videoVolume);
  });
  refreshVolumeControlFromStorage(podcastVolume, "podcastVolume", () => {
    const v = Number(podcastVolume.value);
    podcastPlayer.volume = v / 100;
    podcastPlayer.muted = v === 0;
    podcastVolumeLabel.textContent = `${v}%`;
    podcastMuteBtn.textContent = volumeIconFor(v, podcastPlayer.muted);
    updateRangeFill(podcastVolume);
  });
}

async function loadAllUserMediaData() {
  playlists = appGet("musicPlaylists", {});
  musicPlaylistMeta = appGet("musicPlaylistMeta", {});
  videoPlaylists = appGet("videoPlaylists", {});
  videoPlaylistMeta = appGet("videoPlaylistMeta", {});
  documentaryPlaylists = appGet("documentaryPlaylists", {});
  documentaryPlaylistMeta = appGet("documentaryPlaylistMeta", {});
  moviePlaylists = appGet("moviePlaylists", {});
  moviePlaylistMeta = appGet("moviePlaylistMeta", {});
  comedyPlaylists = appGet("comedyPlaylists", {});
  comedyPlaylistMeta = appGet("comedyPlaylistMeta", {});
  webseriesPlaylists = appGet("webseriesPlaylists", {});
  webseriesPlaylistMeta = appGet("webseriesPlaylistMeta", {});
  gamesPlaylists = appGet("gamesPlaylists", {});
  gamesPlaylistMeta = appGet("gamesPlaylistMeta", {});
  booksPlaylists = appGet("booksPlaylists", {});
  booksPlaylistMeta = appGet("booksPlaylistMeta", {});
  musicPositions = appGet("musicPositions", {});
  videoPositions = appGet("videoPositions", {});
  documentaryPositions = appGet("documentaryPositions", {});
  moviePositions = appGet("moviePositions", {});
  comedyPositions = appGet("comedyPositions", {});
  webseriesPositions = appGet("webseriesPositions", {});
  musicRecent = appGet("musicRecent", []);
  videoRecent = appGet("videoRecent", []);
  podcastRecent = appGet("podcastRecent", []);
  bookmarkRecent = appGet("bookmarkRecent", []);
  bookmarkCollections = appGet("bookmarkCollections", {});
  musicPlaylistSortMode = appGet("musicPlaylistSortMode", "name");
  videoPlaylistSortMode = appGet("videoPlaylistSortMode", "name");
  podcastPlaylistSortMode = appGet("podcastPlaylistSortMode", "name");
  documentaryPlaylistSortMode = appGet("documentaryPlaylistSortMode", "name");
  moviePlaylistSortMode = appGet("moviePlaylistSortMode", "name");
  comedyPlaylistSortMode = appGet("comedyPlaylistSortMode", "name");
  webseriesPlaylistSortMode = appGet("webseriesPlaylistSortMode", "name");
  gamesPlaylistSortMode = appGet("gamesPlaylistSortMode", "name");
  booksPlaylistSortMode = appGet("booksPlaylistSortMode", "name");
  gamevideoPlaylists = appGet("gamevideoPlaylists", {});
  gamevideoPlaylistMeta = appGet("gamevideoPlaylistMeta", {});
  gamemoviePlaylists = appGet("gamemoviePlaylists", {});
  gamemoviePlaylistMeta = appGet("gamemoviePlaylistMeta", {});
  bookvideoPlaylists = appGet("bookvideoPlaylists", {});
  bookvideoPlaylistMeta = appGet("bookvideoPlaylistMeta", {});
  bookmoviePlaylists = appGet("bookmoviePlaylists", {});
  bookmoviePlaylistMeta = appGet("bookmoviePlaylistMeta", {});
  presentationsPlaylists = appGet("presentationsPlaylists", {});
  presentationsPlaylistMeta = appGet("presentationsPlaylistMeta", {});
  gamevideoPositions = appGet("gamevideoPositions", {});
  gamemoviePositions = appGet("gamemoviePositions", {});
  bookvideoPositions = appGet("bookvideoPositions", {});
  bookmoviePositions = appGet("bookmoviePositions", {});
  gamevideoPlaylistSortMode = appGet("gamevideoPlaylistSortMode", "name");
  gamemoviePlaylistSortMode = appGet("gamemoviePlaylistSortMode", "name");
  bookvideoPlaylistSortMode = appGet("bookvideoPlaylistSortMode", "name");
  bookmoviePlaylistSortMode = appGet("bookmoviePlaylistSortMode", "name");
  presentationsPlaylistSortMode = appGet("presentationsPlaylistSortMode", "name");
  Object.keys(QUEUE_TYPES).forEach(type => loadQueue(type));
  await Promise.all([ loadMusicFromDB(), loadVideosFromDB(), loadDocumentaryFromDB(), loadMovieFromDB(), loadComedyFromDB(), loadWebSeriesFromDB(), loadPodcastsFromDB(), loadGamesFromDB(), loadBooksFromDB(), loadBookmarksFromDB(), loadGameVideoFromDB(), loadGameMovieFromDB(), loadBookVideoFromDB(), loadBookMovieFromDB(), loadPresentationsFromDB() ]);
  renderPlaylists();
  renderVideoPlaylists();
  renderDocumentaryPlaylists();
  renderMoviePlaylists();
  renderComedyPlaylists();
  renderWebSeriesPlaylists();
  renderGamesPlaylists();
  renderBooksPlaylists();
  renderGameVideoPlaylists();
  renderGameMoviePlaylists();
  renderBookVideoPlaylists();
  renderBookMoviePlaylists();
  renderPresentationsPlaylists();
  renderMusicRecent();
  renderVideoRecent();
  renderPodcastRecent();
  renderBookmarkRecent();
  renderBookmarkCollections();
  renderCollectionBookmarks();
  renderPlaylistMusic();
  renderPlaylistVideos();
  renderPodcastPlaylistSongs();
  renderPlaylistDocumentary();
  renderPlaylistMovie();
  renderPlaylistComedy();
  renderPlaylistWebSeries();
  renderPlaylistGames();
  renderPlaylistBooks();
  renderPlaylistGameVideo();
  renderPlaylistGameMovie();
  renderPlaylistBookVideo();
  renderPlaylistBookMovie();
  renderPlaylistPresentations();
  Object.keys(QUEUE_TYPES).forEach(type => renderQueue(type));
  refreshVolumeControlFromStorage(musicVolume, "musicVolume", () => {
    const v = Number(musicVolume.value);
    audioPlayer.volume = v / 100;
    audioPlayer.muted = v === 0;
    musicVolumeLabel.textContent = `${v}%`;
    musicMuteBtn.textContent = volumeIconFor(v, audioPlayer.muted);
    updateRangeFill(musicVolume);
  });
  refreshVolumeControlFromStorage(videoVolume, "videoVolume", () => {
    const v = Number(videoVolume.value);
    videoPlayer.volume = v / 100;
    videoPlayer.muted = v === 0;
    videoVolumeLabel.textContent = `${v}%`;
    videoMuteBtn.textContent = volumeIconFor(v, videoPlayer.muted);
    updateRangeFill(videoVolume);
  });
  refreshVolumeControlFromStorage(podcastVolume, "podcastVolume", () => {
    const v = Number(podcastVolume.value);
    podcastPlayer.volume = v / 100;
    podcastPlayer.muted = v === 0;
    podcastVolumeLabel.textContent = `${v}%`;
    podcastMuteBtn.textContent = volumeIconFor(v, podcastPlayer.muted);
    updateRangeFill(podcastVolume);
  });
  await initHistory();
  runAutoMergeDuplicates();
  resumeLastPlayedMusic();
  resumeLastPlayedVideo();
  resumeLastPlayedPodcast();
}

async function initAppData() {
  const dbTargets = [ {
    label: "app settings",
    open: openAppDB,
    assign: db => appDB = db,
    message: "Could not open local settings storage. Playlists, saved positions, and preferences will not be saved this session."
  }, {
    label: "music",
    open: openMusicDB,
    assign: db => musicDB = db,
    message: "Could not open the local song database."
  }, {
    label: "video",
    open: openVideoDB,
    assign: db => videoDB = db,
    message: "Could not open the local video database."
  }, {
    label: "documentaries",
    open: openDocumentaryDB,
    assign: db => documentaryDB = db,
    message: "Could not open the local documentary database."
  }, {
    label: "movies",
    open: openMovieDB,
    assign: db => movieDB = db,
    message: "Could not open the local movie database."
  }, {
    label: "comedy",
    open: openComedyDB,
    assign: db => comedyDB = db,
    message: "Could not open the local comedy database."
  }, {
    label: "web series",
    open: openWebSeriesDB,
    assign: db => webseriesDB = db,
    message: "Could not open the local web series database."
  }, {
    label: "podcasts",
    open: openPodcastDB,
    assign: db => podcastDB = db,
    message: "Could not open the local podcast database. Podcasts will not be saved this session."
  }, {
    label: "games",
    open: openGamesDB,
    assign: db => gamesDB = db,
    message: "Could not open the local games database."
  }, {
    label: "books",
    open: openBooksDB,
    assign: db => booksDB = db,
    message: "Could not open the local books database."
  }, {
    label: "bookmarks",
    open: openBookmarkDB,
    assign: db => bookmarkDB = db,
    message: "Could not open the local bookmark database."
  }, {
    label: "game videos",
    open: openGameVideoDB,
    assign: db => gamevideoDB = db,
    message: "Could not open the local game video database."
  }, {
    label: "game movies",
    open: openGameMovieDB,
    assign: db => gamemovieDB = db,
    message: "Could not open the local game movie database."
  }, {
    label: "book videos",
    open: openBookVideoDB,
    assign: db => bookvideoDB = db,
    message: "Could not open the local book video database."
  }, {
    label: "book movies",
    open: openBookMovieDB,
    assign: db => bookmovieDB = db,
    message: "Could not open the local book movie database."
  }, {
    label: "presentations",
    open: openPresentationsDB,
    assign: db => presentationsDB = db,
    message: "Could not open the local presentations database."
  } ];
  const results = await Promise.allSettled(dbTargets.map(target => target.open().then(db => target.assign(db))));
  const failures = [];
  results.forEach((result, i) => {
    if (result.status === "rejected") {
      console.error(`IndexedDB (${dbTargets[i].label}) failed to open`, result.reason);
      failures.push(dbTargets[i].message);
    }
  });
  if (appDB) {
    try {
      await loadAllAppData(appDB);
    } catch (err) {
      console.error("Failed to load app settings data", err);
      failures.push("Could not load saved settings and playlists.");
    }
  }
  if (failures.length) {
    console.warn("Some local databases failed to open:", failures);
    alert(`Some local storage could not be accessed on this device:

${failures.join("\n")}

Affected sections may not save data this session.`);
  }
  bookmarkSortMode = appGet("bookmarkSortMode", "newest");
  if (bookmarkSortSelect) {
    bookmarkSortSelect.value = bookmarkSortMode;
    syncCustomDropdown(bookmarkSortSelect);
  }
  setupVolumeControl(audioPlayer, musicVolume, musicMuteBtn, musicVolumeLabel, "musicVolume");
  setupSpeedControl(audioPlayer, musicSpeedGroup, "musicSpeed");
  setupVolumeControl(videoPlayer, videoVolume, videoMuteBtn, videoVolumeLabel, "videoVolume");
  setupSpeedControl(videoPlayer, videoSpeedGroup, "videoSpeed");
  setupVolumeControl(documentaryPlayer, documentaryVolume, documentaryMuteBtn, documentaryVolumeLabel, "documentaryVolume");
  setupSpeedControl(documentaryPlayer, documentarySpeedGroup, "documentarySpeed");
  setupVolumeControl(moviePlayer, movieVolume, movieMuteBtn, movieVolumeLabel, "movieVolume");
  setupSpeedControl(moviePlayer, movieSpeedGroup, "movieSpeed");
  setupVolumeControl(comedyPlayer, comedyVolume, comedyMuteBtn, comedyVolumeLabel, "comedyVolume");
  setupSpeedControl(comedyPlayer, comedySpeedGroup, "comedySpeed");
  setupVolumeControl(webseriesPlayer, webseriesVolume, webseriesMuteBtn, webseriesVolumeLabel, "webseriesVolume");
  setupSpeedControl(webseriesPlayer, webseriesSpeedGroup, "webseriesSpeed");
  setupVolumeControl(podcastPlayer, podcastVolume, podcastMuteBtn, podcastVolumeLabel, "podcastVolume");
  setupSpeedControl(podcastPlayer, podcastSpeedGroup, "podcastSpeed");
  setupVolumeControl(gamevideoPlayer, gamevideoVolume, gamevideoMuteBtn, gamevideoVolumeLabel, "gamevideoVolume");
  setupSpeedControl(gamevideoPlayer, gamevideoSpeedGroup, "gamevideoSpeed");
  setupVolumeControl(gamemoviePlayer, gamemovieVolume, gamemovieMuteBtn, gamemovieVolumeLabel, "gamemovieVolume");
  setupSpeedControl(gamemoviePlayer, gamemovieSpeedGroup, "gamemovieSpeed");
  setupVolumeControl(bookvideoPlayer, bookvideoVolume, bookvideoMuteBtn, bookvideoVolumeLabel, "bookvideoVolume");
  setupSpeedControl(bookvideoPlayer, bookvideoSpeedGroup, "bookvideoSpeed");
  setupVolumeControl(bookmoviePlayer, bookmovieVolume, bookmovieMuteBtn, bookmovieVolumeLabel, "bookmovieVolume");
  setupSpeedControl(bookmoviePlayer, bookmovieSpeedGroup, "bookmovieSpeed");
  updateRangeFill(musicProgress);
  updateRangeFill(videoProgress);
  updateRangeFill(documentaryProgress);
  updateRangeFill(movieProgress);
  updateRangeFill(comedyProgress);
  updateRangeFill(webseriesProgress);
  updateRangeFill(podcastProgress);
  updateRangeFill(gamevideoProgress);
  updateRangeFill(gamemovieProgress);
  updateRangeFill(bookvideoProgress);
  updateRangeFill(bookmovieProgress);
  userAccount = new UserAccountSystem;
  const PAGE_SHOW_METHODS = {
    hub: "showTerminalHubPage",
    music: "showMusicPage",
    video: "showVideoPage",
    documentary: "showDocumentaryPage",
    movie: "showMoviePage",
    comedy: "showComedyPage",
    webseries: "showWebSeriesPage",
    podcast: "showPodcastPage",
    games: "showGamesPage",
    books: "showBooksPage",
    bookmarks: "showBookmarksPage",
    account: "showAccountPage",
    gamevideo: "showGameVideoPage",
    gamemovie: "showGameMoviePage",
    bookvideo: "showBookVideoPage",
    bookmovie: "showBookMoviePage",
    presentations: "showPresentationsPage"
  };
  document.querySelectorAll('button[id^="goto-"]').forEach(btn => {
    const match = btn.id.match(/^goto-([a-z]+)-from-([a-z]+)$/);
    if (!match) return;
    const targetKey = match[1];
    const sourceKey = match[2];
    const method = PAGE_SHOW_METHODS[targetKey];
    if (!method || typeof userAccount[method] !== "function") return;
    btn.addEventListener("click", () => {
      if (targetKey === "account" && PAGE_SHOW_METHODS[sourceKey]) userAccount.lastActiveTerminal = sourceKey;
      userAccount[method]();
    });
  });
}

function setupBannerHandling() {
  const banner = document.getElementById("no-account-banner");
  const dismissBtn = document.getElementById("dismiss-account-banner");
  const ctaBtn = document.getElementById("account-banner-cta");
  if (dismissBtn) {
    dismissBtn.addEventListener("click", e => {
      e.preventDefault();
      dismissFirstTimeBanner();
    });
  }
  if (ctaBtn) {
    ctaBtn.addEventListener("click", () => {
      const targetTab = ctaBtn.dataset.tab || "signup";
      const tabBtn = document.querySelector(`.tab-btn[data-tab="${targetTab}"]`);
      if (tabBtn) tabBtn.click();
      const identifierInput = document.getElementById("signup-username");
      if (identifierInput) identifierInput.focus();
      dismissFirstTimeBanner();
    });
  }
}

let documentary = [];

let currentDocumentaryId = null;

let documentaryPositions = {};

let documentaryPlaylists = {};

let documentaryPlaylistMeta = {};

let currentDocumentaryPlaylist = null;

let documentaryPlaylistPlaying = false;

let documentaryLoopPlaylist = false;

let documentaryPlaylistSortMode = "name";

let documentaryRepeat = false;

let lastDocumentaryPositionSave = 0;

let documentaryDB;

const documentarySearch = document.getElementById("documentary-search");

const documentaryUpload = document.getElementById("documentary-upload");

const documentaryList = document.getElementById("documentary-list");

const documentaryCount = document.getElementById("documentary-count");

const currentDocumentaryDisplay = document.getElementById("current-documentary");

const documentaryPlayer = document.getElementById("documentary-player");

const documentaryProgress = document.getElementById("documentary-progress");

const documentaryCurrentTimeEl = document.getElementById("documentary-current-time");

const documentaryDurationEl = document.getElementById("documentary-duration");

const playPauseDocumentaryBtn = document.getElementById("play-pause-documentary");

const nextDocumentaryBtn = document.getElementById("next-documentary");

const prevDocumentaryBtn = document.getElementById("prev-documentary");

const toggleRepeatDocumentaryBtn = document.getElementById("toggle-repeat-documentary");

const documentaryVolume = document.getElementById("documentary-volume");

const documentaryMuteBtn = document.getElementById("documentary-mute-btn");

const documentaryVolumeLabel = document.getElementById("documentary-volume-label");

const documentarySpeedGroup = document.getElementById("documentary-speed-group");

const documentaryPlaylistsEl = document.getElementById("documentary-playlists");

const documentaryPlaylistToolbarEl = document.getElementById("documentary-playlist-toolbar");

const documentaryPlaylistName = document.getElementById("documentary-playlist-name");

const playlistDocumentary = document.getElementById("playlist-documentary");

const documentaryPlaylistTitle = document.getElementById("documentary-playlist-title");

const documentaryPlaylistHeaderEl = document.getElementById("documentary-playlist-header");

function openDocumentaryDB() {
  return openTerminalDB("DocumentaryPlayerDB", [ {
    name: "documentary"
  } ]);
}

async function loadDocumentaryFromDB() {
  if (!documentaryDB || !currentUserId) {
    documentary.length = 0;
    renderDocumentary(documentarySearch.value);
    return;
  }
  const rows = await loadUserRecordsIndexed(documentaryDB, "documentary", currentUserId);
  documentary.length = 0;
  documentary.push(...rows);
  restoreListSortMode("documentary", documentary);
  renderDocumentary(documentarySearch.value);
}

function renderDocumentary(filter = "") {
  const f = filter.toLowerCase();
  const visible = documentary.filter(item => !f || item.name.toLowerCase().includes(f));
  renderListBatched(documentaryList, visible, item => {
    const li = document.createElement("li");
    if (item.id === currentDocumentaryId) li.classList.add("selected");
    const name = document.createElement("span");
    name.textContent = item.name;
    const playBtn = document.createElement("button");
    playBtn.textContent = "▶";
    playBtn.className = "media-row-play-btn";
    playBtn.addEventListener("click", () => playDocumentaryById(item.id));
    const deleteBtn = document.createElement("button");
    deleteBtn.textContent = "✕";
    deleteBtn.addEventListener("click", () => deleteDocumentaryById(item.id));
    li.append(name, playBtn, deleteBtn);
    return li;
  });
  documentaryCount.textContent = `Total Documentaries: ${documentary.length}`;
}

function playDocumentaryById(id, isResume) {
  const item = documentary.find(v => v.id === id);
  if (!item) return;
  let url;
  try {
    url = URL.createObjectURL(item.blob);
  } catch (err) {
    console.error("Failed to create a playback URL", err);
    alert("Could not load this file for playback.");
    return;
  }
  currentDocumentaryId = id;
  if (documentaryPlayer.dataset.url) URL.revokeObjectURL(documentaryPlayer.dataset.url);
  documentaryPlayer.src = url;
  documentaryPlayer.dataset.url = url;
  const resumeAt = documentaryPositions[id];
  if (resumeAt) {
    const restorePosition = () => {
      if (resumeAt < documentaryPlayer.duration - 2) documentaryPlayer.currentTime = resumeAt;
      documentaryPlayer.removeEventListener("loadedmetadata", restorePosition);
    };
    documentaryPlayer.addEventListener("loadedmetadata", restorePosition);
  }
  currentDocumentaryDisplay.textContent = item.name;
  documentaryPlayer.play().then(() => {
    playPauseDocumentaryBtn.textContent = "Pause";
  }).catch(err => {
    console.error("Playback failed to start", err);
    playPauseDocumentaryBtn.textContent = "Play";
  });
  renderDocumentary(documentarySearch.value);
}

function stopDocumentary() {
  currentDocumentaryId = null;
  documentaryPlayer.pause();
  documentaryPlayer.removeAttribute("src");
  if (documentaryPlayer.dataset.url) {
    URL.revokeObjectURL(documentaryPlayer.dataset.url);
    delete documentaryPlayer.dataset.url;
  }
  currentDocumentaryDisplay.textContent = "No documentary selected";
  playPauseDocumentaryBtn.textContent = "Play";
  renderDocumentary(documentarySearch.value);
}

function playNextDocumentary() {
  const queuedId = consumeQueueNext("documentary");
  if (queuedId !== null) return playDocumentaryById(queuedId);
  if (documentaryPlaylistPlaying && currentDocumentaryPlaylist) {
    const list = getActivePlaylistIds(documentaryPlaylistCtx());
    const shuffle = !isSmartPlaylist(currentDocumentaryPlaylist) && getPlaylistMeta(documentaryPlaylistMeta, currentDocumentaryPlaylist).shuffle;
    const next = pickNextInList(list, currentDocumentaryId, shuffle);
    if (next !== null) return playDocumentaryById(next);
    if (documentaryLoopPlaylist && list.length) return playDocumentaryById(shuffle ? list[Math.floor(Math.random() * list.length)] : list[0]);
    documentaryPlaylistPlaying = false;
    return;
  }
  if (!documentary.length) return;
  const idx = documentary.findIndex(v => v.id === currentDocumentaryId);
  const nextIdx = idx === -1 ? 0 : (idx + 1) % documentary.length;
  playDocumentaryById(documentary[nextIdx].id);
}

function playPrevDocumentary() {
  if (documentaryPlaylistPlaying && currentDocumentaryPlaylist) {
    const list = getActivePlaylistIds(documentaryPlaylistCtx());
    const idx = list.indexOf(currentDocumentaryId);
    if (idx > 0) return playDocumentaryById(list[idx - 1]);
    return;
  }
  if (!documentary.length) return;
  const idx = documentary.findIndex(v => v.id === currentDocumentaryId);
  const prevIdx = idx <= 0 ? documentary.length - 1 : idx - 1;
  playDocumentaryById(documentary[prevIdx].id);
}

function deleteDocumentaryById(id) {
  if (!documentaryDB) return;
  if (!confirm("Delete this item?")) return;
  const tx = documentaryDB.transaction("documentary", "readwrite");
  tx.objectStore("documentary").delete(id);
  tx.oncomplete = () => {
    if (currentDocumentaryId === id) stopDocumentary();
    delete documentaryPositions[id];
    appSet("documentaryPositions", documentaryPositions);
    loadDocumentaryFromDB();
  };
}

documentaryUpload.addEventListener("change", async e => {
  if (!documentaryDB || !currentUserId) return;
  const rawFiles = [ ...e.target.files ];
  if (!rawFiles.length) return;
  const files = filterUploadedMediaFiles(rawFiles, "video");
  if (!files.length) {
    documentaryUpload.value = "";
    return;
  }
  const existingKeys = new Set(documentary.map(v => `${v.name.toLowerCase()}|${v.blob.size}`));
  const newFiles = files.filter(f => !existingKeys.has(`${f.name.toLowerCase()}|${f.size}`));
  const skippedCount = files.length - newFiles.length;
  if (!newFiles.length) {
    documentaryUpload.value = "";
    if (skippedCount) alert(`Skipped ${skippedCount} duplicate file(s) already in your library.`);
    return;
  }
  const tx = documentaryDB.transaction("documentary", "readwrite");
  const store = tx.objectStore("documentary");
  newFiles.forEach(file => {
    store.add({
      name: file.name,
      blob: file,
      userId: currentUserId
    });
  });
  tx.oncomplete = () => {
    documentaryUpload.value = "";
    loadDocumentaryFromDB();
    if (skippedCount) alert(`Added ${newFiles.length} file(s). Skipped ${skippedCount} duplicate(s).`);
  };
  tx.onerror = () => {
    console.error("Failed to save uploaded file(s)", tx.error);
    alert("Could not save the uploaded file(s).");
  };
});

documentarySearch.addEventListener("input", debounce(() => renderDocumentary(documentarySearch.value)));

document.getElementById("btn-shuffle-documentary").addEventListener("click", () => {
  shuffleArray(documentary);
  saveListSortMode("documentary", "shuffle", documentary);
  renderDocumentary(documentarySearch.value);
});

document.getElementById("btn-sort-az-documentary").addEventListener("click", () => {
  documentary.sort((a, b) => a.name.localeCompare(b.name));
  saveListSortMode("documentary", "az", documentary);
  renderDocumentary(documentarySearch.value);
});

document.getElementById("btn-sort-za-documentary").addEventListener("click", () => {
  documentary.sort((a, b) => b.name.localeCompare(a.name));
  saveListSortMode("documentary", "za", documentary);
  renderDocumentary(documentarySearch.value);
});

playPauseDocumentaryBtn.addEventListener("click", () => {
  if (!currentDocumentaryId && documentary.length) return playDocumentaryById(documentary[0].id);
  if (documentaryPlayer.paused) {
    documentaryPlayer.play();
    playPauseDocumentaryBtn.textContent = "Pause";
  } else {
    documentaryPlayer.pause();
    playPauseDocumentaryBtn.textContent = "Play";
  }
});

nextDocumentaryBtn.addEventListener("click", () => playNextDocumentary());

prevDocumentaryBtn.addEventListener("click", () => playPrevDocumentary());

toggleRepeatDocumentaryBtn.addEventListener("click", () => {
  documentaryRepeat = !documentaryRepeat;
  documentaryPlayer.loop = documentaryRepeat;
  toggleRepeatDocumentaryBtn.textContent = `Repeat: ${documentaryRepeat ? "On" : "Off"}`;
});

documentaryPlayer.addEventListener("timeupdate", () => {
  if (!documentaryPlayer.duration) return;
  documentaryProgress.value = documentaryPlayer.currentTime / documentaryPlayer.duration * 100;
  updateRangeFill(documentaryProgress);
  documentaryCurrentTimeEl.textContent = formatTime(documentaryPlayer.currentTime);
  documentaryDurationEl.textContent = formatTime(documentaryPlayer.duration);
  if (currentDocumentaryId !== null) {
    const now = Date.now();
    if (now - lastDocumentaryPositionSave > POSITION_SAVE_INTERVAL) {
      lastDocumentaryPositionSave = now;
      documentaryPositions[currentDocumentaryId] = documentaryPlayer.currentTime;
      appSet("documentaryPositions", documentaryPositions);
    }
  }
});

documentaryProgress.addEventListener("input", () => {
  if (documentaryPlayer.duration) documentaryPlayer.currentTime = documentaryProgress.value / 100 * documentaryPlayer.duration;
  updateRangeFill(documentaryProgress);
});

documentaryPlayer.addEventListener("pause", () => {
  if (currentDocumentaryId !== null && documentaryPlayer.duration) {
    documentaryPositions[currentDocumentaryId] = documentaryPlayer.currentTime;
    appSet("documentaryPositions", documentaryPositions);
  }
});

documentaryPlayer.addEventListener("ended", () => {
  if (currentDocumentaryId !== null) {
    delete documentaryPositions[currentDocumentaryId];
    appSet("documentaryPositions", documentaryPositions);
  }
  playNextDocumentary();
});

document.getElementById("forward-10-documentary").addEventListener("click", () => {
  documentaryPlayer.currentTime += 10;
});

document.getElementById("rewind-10-documentary").addEventListener("click", () => {
  documentaryPlayer.currentTime = Math.max(0, documentaryPlayer.currentTime - 10);
});

function documentaryPlaylistCtx() {
  return {
    playlistsObj: documentaryPlaylists,
    metaObj: documentaryPlaylistMeta,
    mediaArray: () => documentary,
    historyType: "documentary",
    listEl: documentaryPlaylistsEl,
    toolbarEl: documentaryPlaylistToolbarEl,
    tracksEl: playlistDocumentary,
    headerEl: documentaryPlaylistHeaderEl,
    titleEl: documentaryPlaylistTitle,
    getCurrent: () => currentDocumentaryPlaylist,
    setCurrent: v => {
      currentDocumentaryPlaylist = v;
    },
    getSortMode: () => documentaryPlaylistSortMode,
    setSortMode: v => {
      documentaryPlaylistSortMode = v;
      appSet("documentaryPlaylistSortMode", v);
    },
    saveFn: saveDocumentaryPlaylists,
    saveMetaFn: saveDocumentaryPlaylistMeta,
    renderNamesFn: renderDocumentaryPlaylists,
    renderTracksFn: renderPlaylistDocumentary,
    selectFn: selectDocumentaryPlaylist,
    playByIdFn: id => playDocumentaryById(id),
    currentPlayingId: () => currentDocumentaryId,
    setPlaying: v => {
      documentaryPlaylistPlaying = v;
    }
  };
}

function renderDocumentaryPlaylists() {
  renderPlaylistNamesGeneric(documentaryPlaylistCtx());
}

function selectDocumentaryPlaylist(name) {
  currentDocumentaryPlaylist = name;
  documentaryPlaylistTitle.textContent = isSmartPlaylist(name) ? smartPlaylistLabel(name) : name;
  renderPlaylistDocumentary();
  renderDocumentaryPlaylists();
}

function renderPlaylistDocumentary() {
  renderPlaylistTracksGeneric(documentaryPlaylistCtx());
}

function saveDocumentaryPlaylists() {
  appSet("documentaryPlaylists", documentaryPlaylists);
}

function saveDocumentaryPlaylistMeta() {
  appSet("documentaryPlaylistMeta", documentaryPlaylistMeta);
}

document.getElementById("btn-create-documentary-playlist").addEventListener("click", () => {
  const name = documentaryPlaylistName.value.trim();
  if (!name || documentaryPlaylists[name] || isSmartPlaylist(name)) return alert("Invalid or duplicate playlist name");
  documentaryPlaylists[name] = [];
  getPlaylistMeta(documentaryPlaylistMeta, name);
  documentaryPlaylistName.value = "";
  renderDocumentaryPlaylists();
  saveDocumentaryPlaylists();
  saveDocumentaryPlaylistMeta();
});

document.getElementById("btn-delete-documentary-playlist").addEventListener("click", () => {
  if (!currentDocumentaryPlaylist || isSmartPlaylist(currentDocumentaryPlaylist)) return alert("Select a playlist first");
  delete documentaryPlaylists[currentDocumentaryPlaylist];
  delete documentaryPlaylistMeta[currentDocumentaryPlaylist];
  currentDocumentaryPlaylist = null;
  documentaryPlaylistTitle.textContent = "Select a playlist";
  renderPlaylistDocumentary();
  renderDocumentaryPlaylists();
  saveDocumentaryPlaylists();
  saveDocumentaryPlaylistMeta();
});

document.getElementById("btn-add-selected-documentary-to-playlist").addEventListener("click", () => {
  if (!currentDocumentaryPlaylist || isSmartPlaylist(currentDocumentaryPlaylist)) return alert("Select a playlist first");
  document.querySelectorAll("#documentary-list input[type=checkbox]:checked").forEach(cb => {
    const id = Number(cb.dataset.id);
    if (!documentaryPlaylists[currentDocumentaryPlaylist].includes(id)) documentaryPlaylists[currentDocumentaryPlaylist].push(id);
  });
  touchPlaylistMeta(documentaryPlaylistMeta, currentDocumentaryPlaylist);
  renderPlaylistDocumentary();
  renderDocumentaryPlaylists();
  saveDocumentaryPlaylists();
  saveDocumentaryPlaylistMeta();
});

document.getElementById("btn-add-all-documentary-to-playlist").addEventListener("click", () => {
  if (!currentDocumentaryPlaylist || isSmartPlaylist(currentDocumentaryPlaylist)) return alert("Select a playlist first");
  documentary.forEach(item => {
    if (!documentaryPlaylists[currentDocumentaryPlaylist].includes(item.id)) documentaryPlaylists[currentDocumentaryPlaylist].push(item.id);
  });
  touchPlaylistMeta(documentaryPlaylistMeta, currentDocumentaryPlaylist);
  renderPlaylistDocumentary();
  renderDocumentaryPlaylists();
  saveDocumentaryPlaylists();
  saveDocumentaryPlaylistMeta();
});

document.getElementById("btn-remove-documentary-from-playlist").addEventListener("click", () => {
  if (!currentDocumentaryPlaylist || isSmartPlaylist(currentDocumentaryPlaylist)) return;
  const toRemove = Array.from(playlistDocumentary.querySelectorAll("input[type=checkbox]:checked")).map(cb => Number(cb.dataset.id));
  documentaryPlaylists[currentDocumentaryPlaylist] = documentaryPlaylists[currentDocumentaryPlaylist].filter(id => !toRemove.includes(id));
  touchPlaylistMeta(documentaryPlaylistMeta, currentDocumentaryPlaylist);
  renderPlaylistDocumentary();
  renderDocumentaryPlaylists();
  saveDocumentaryPlaylists();
  saveDocumentaryPlaylistMeta();
});

document.getElementById("btn-clear-documentary-playlist").addEventListener("click", () => {
  if (!currentDocumentaryPlaylist || isSmartPlaylist(currentDocumentaryPlaylist)) return;
  documentaryPlaylists[currentDocumentaryPlaylist] = [];
  touchPlaylistMeta(documentaryPlaylistMeta, currentDocumentaryPlaylist);
  renderPlaylistDocumentary();
  renderDocumentaryPlaylists();
  saveDocumentaryPlaylists();
  saveDocumentaryPlaylistMeta();
});

document.getElementById("btn-play-documentary-playlist").addEventListener("click", () => {
  const ids = getActivePlaylistIds(documentaryPlaylistCtx());
  if (!currentDocumentaryPlaylist || !ids.length) return alert("Select a playlist with documentaries");
  documentaryPlaylistPlaying = true;
  playDocumentaryById(ids[0]);
});

document.getElementById("btn-export-documentary-playlist").addEventListener("click", () => {
  exportPlaylistFile(currentDocumentaryPlaylist, currentDocumentaryPlaylist ? getActivePlaylistIds(documentaryPlaylistCtx()) : null, documentary);
});

document.getElementById("documentary-playlist-import").addEventListener("change", async e => {
  const file = e.target.files[0];
  if (!file) return;
  try {
    await importPlaylistFile(file, documentaryDB, "documentary", documentary, documentaryPlaylists, saveDocumentaryPlaylists, renderPlaylistDocumentary, renderDocumentaryPlaylists, selectDocumentaryPlaylist, documentaryPlaylistMeta, saveDocumentaryPlaylistMeta, "video");
  } finally {
    e.target.value = "";
  }
  renderDocumentary(documentarySearch.value);
});

PLAYLIST_FOLDER_IMPORT_HANDLERS["documentary-playlist-import"] = async (files, folderName) => {
  await importPlaylistFolder(files, folderName, documentaryDB, "documentary", documentary, documentaryPlaylists, saveDocumentaryPlaylists, renderPlaylistDocumentary, renderDocumentaryPlaylists, selectDocumentaryPlaylist, documentaryPlaylistMeta, saveDocumentaryPlaylistMeta, "video");
  renderDocumentary(documentarySearch.value);
};

(function enablePlaylistPanelDrop(wrapId, isValidId, getCurrentName, addToPlaylist, saveFn, renderListFn, renderNamesFn) {
  const wrap = document.getElementById(wrapId);
  if (!wrap) return;
  wrap.addEventListener("dragover", e => {
    if (!getCurrentName() || !e.dataTransfer.types.includes("text/plain")) return;
    e.preventDefault();
    e.dataTransfer.dropEffect = "copy";
    wrap.classList.add("drag-over");
  });
  wrap.addEventListener("dragleave", e => {
    if (!wrap.contains(e.relatedTarget)) wrap.classList.remove("drag-over");
  });
  wrap.addEventListener("drop", e => {
    e.preventDefault();
    wrap.classList.remove("drag-over");
    const name = getCurrentName();
    if (!name) return;
    const id = Number(e.dataTransfer.getData("text/plain"));
    if (!id || !isValidId(id)) return;
    addToPlaylist(name, id);
    saveFn();
    renderListFn();
    renderNamesFn();
  });
})("playlist-documentary-wrap", id => !!documentary.find(d => d.id === id), () => currentDocumentaryPlaylist, (name, id) => {
  if (!documentaryPlaylists[name].includes(id)) documentaryPlaylists[name].push(id);
}, saveDocumentaryPlaylists, renderPlaylistDocumentary, renderDocumentaryPlaylists);

let movie = [];

let currentMovieId = null;

let moviePositions = {};

let moviePlaylists = {};

let moviePlaylistMeta = {};

let currentMoviePlaylist = null;

let moviePlaylistPlaying = false;

let movieLoopPlaylist = false;

let moviePlaylistSortMode = "name";

let movieRepeat = false;

let lastMoviePositionSave = 0;

let movieDB;

const movieSearch = document.getElementById("movie-search");

const movieUpload = document.getElementById("movie-upload");

const movieList = document.getElementById("movie-list");

const movieCount = document.getElementById("movie-count");

const currentMovieDisplay = document.getElementById("current-movie");

const moviePlayer = document.getElementById("movie-player");

const movieProgress = document.getElementById("movie-progress");

const movieCurrentTimeEl = document.getElementById("movie-current-time");

const movieDurationEl = document.getElementById("movie-duration");

const playPauseMovieBtn = document.getElementById("play-pause-movie");

const nextMovieBtn = document.getElementById("next-movie");

const prevMovieBtn = document.getElementById("prev-movie");

const toggleRepeatMovieBtn = document.getElementById("toggle-repeat-movie");

const movieVolume = document.getElementById("movie-volume");

const movieMuteBtn = document.getElementById("movie-mute-btn");

const movieVolumeLabel = document.getElementById("movie-volume-label");

const movieSpeedGroup = document.getElementById("movie-speed-group");

const moviePlaylistsEl = document.getElementById("movie-playlists");

const moviePlaylistToolbarEl = document.getElementById("movie-playlist-toolbar");

const moviePlaylistName = document.getElementById("movie-playlist-name");

const playlistMovie = document.getElementById("playlist-movie");

const moviePlaylistTitle = document.getElementById("movie-playlist-title");

const moviePlaylistHeaderEl = document.getElementById("movie-playlist-header");

function openMovieDB() {
  return openTerminalDB("MoviePlayerDB", [ {
    name: "movie"
  } ]);
}

async function loadMovieFromDB() {
  if (!movieDB || !currentUserId) {
    movie.length = 0;
    renderMovie(movieSearch.value);
    return;
  }
  const rows = await loadUserRecordsIndexed(movieDB, "movie", currentUserId);
  movie.length = 0;
  movie.push(...rows);
  restoreListSortMode("movie", movie);
  renderMovie(movieSearch.value);
}

function renderMovie(filter = "") {
  const f = filter.toLowerCase();
  const visible = movie.filter(item => !f || item.name.toLowerCase().includes(f));
  renderListBatched(movieList, visible, item => {
    const li = document.createElement("li");
    if (item.id === currentMovieId) li.classList.add("selected");
    const name = document.createElement("span");
    name.textContent = item.name;
    const playBtn = document.createElement("button");
    playBtn.textContent = "▶";
    playBtn.className = "media-row-play-btn";
    playBtn.addEventListener("click", () => playMovieById(item.id));
    const deleteBtn = document.createElement("button");
    deleteBtn.textContent = "✕";
    deleteBtn.addEventListener("click", () => deleteMovieById(item.id));
    li.append(name, playBtn, deleteBtn);
    return li;
  });
  movieCount.textContent = `Total Movies: ${movie.length}`;
}

function playMovieById(id, isResume) {
  const item = movie.find(v => v.id === id);
  if (!item) return;
  let url;
  try {
    url = URL.createObjectURL(item.blob);
  } catch (err) {
    console.error("Failed to create a playback URL", err);
    alert("Could not load this file for playback.");
    return;
  }
  currentMovieId = id;
  if (moviePlayer.dataset.url) URL.revokeObjectURL(moviePlayer.dataset.url);
  moviePlayer.src = url;
  moviePlayer.dataset.url = url;
  const resumeAt = moviePositions[id];
  if (resumeAt) {
    const restorePosition = () => {
      if (resumeAt < moviePlayer.duration - 2) moviePlayer.currentTime = resumeAt;
      moviePlayer.removeEventListener("loadedmetadata", restorePosition);
    };
    moviePlayer.addEventListener("loadedmetadata", restorePosition);
  }
  currentMovieDisplay.textContent = item.name;
  moviePlayer.play().then(() => {
    playPauseMovieBtn.textContent = "Pause";
  }).catch(err => {
    console.error("Playback failed to start", err);
    playPauseMovieBtn.textContent = "Play";
  });
  renderMovie(movieSearch.value);
}

function stopMovie() {
  currentMovieId = null;
  moviePlayer.pause();
  moviePlayer.removeAttribute("src");
  if (moviePlayer.dataset.url) {
    URL.revokeObjectURL(moviePlayer.dataset.url);
    delete moviePlayer.dataset.url;
  }
  currentMovieDisplay.textContent = "No movie selected";
  playPauseMovieBtn.textContent = "Play";
  renderMovie(movieSearch.value);
}

function playNextMovie() {
  const queuedId = consumeQueueNext("movie");
  if (queuedId !== null) return playMovieById(queuedId);
  if (moviePlaylistPlaying && currentMoviePlaylist) {
    const list = getActivePlaylistIds(moviePlaylistCtx());
    const shuffle = !isSmartPlaylist(currentMoviePlaylist) && getPlaylistMeta(moviePlaylistMeta, currentMoviePlaylist).shuffle;
    const next = pickNextInList(list, currentMovieId, shuffle);
    if (next !== null) return playMovieById(next);
    if (movieLoopPlaylist && list.length) return playMovieById(shuffle ? list[Math.floor(Math.random() * list.length)] : list[0]);
    moviePlaylistPlaying = false;
    return;
  }
  if (!movie.length) return;
  const idx = movie.findIndex(v => v.id === currentMovieId);
  const nextIdx = idx === -1 ? 0 : (idx + 1) % movie.length;
  playMovieById(movie[nextIdx].id);
}

function playPrevMovie() {
  if (moviePlaylistPlaying && currentMoviePlaylist) {
    const list = getActivePlaylistIds(moviePlaylistCtx());
    const idx = list.indexOf(currentMovieId);
    if (idx > 0) return playMovieById(list[idx - 1]);
    return;
  }
  if (!movie.length) return;
  const idx = movie.findIndex(v => v.id === currentMovieId);
  const prevIdx = idx <= 0 ? movie.length - 1 : idx - 1;
  playMovieById(movie[prevIdx].id);
}

function deleteMovieById(id) {
  if (!movieDB) return;
  if (!confirm("Delete this item?")) return;
  const tx = movieDB.transaction("movie", "readwrite");
  tx.objectStore("movie").delete(id);
  tx.oncomplete = () => {
    if (currentMovieId === id) stopMovie();
    delete moviePositions[id];
    appSet("moviePositions", moviePositions);
    loadMovieFromDB();
  };
}

movieUpload.addEventListener("change", async e => {
  if (!movieDB || !currentUserId) return;
  const rawFiles = [ ...e.target.files ];
  if (!rawFiles.length) return;
  const files = filterUploadedMediaFiles(rawFiles, "video");
  if (!files.length) {
    movieUpload.value = "";
    return;
  }
  const existingKeys = new Set(movie.map(v => `${v.name.toLowerCase()}|${v.blob.size}`));
  const newFiles = files.filter(f => !existingKeys.has(`${f.name.toLowerCase()}|${f.size}`));
  const skippedCount = files.length - newFiles.length;
  if (!newFiles.length) {
    movieUpload.value = "";
    if (skippedCount) alert(`Skipped ${skippedCount} duplicate file(s) already in your library.`);
    return;
  }
  const tx = movieDB.transaction("movie", "readwrite");
  const store = tx.objectStore("movie");
  newFiles.forEach(file => {
    store.add({
      name: file.name,
      blob: file,
      userId: currentUserId
    });
  });
  tx.oncomplete = () => {
    movieUpload.value = "";
    loadMovieFromDB();
    if (skippedCount) alert(`Added ${newFiles.length} file(s). Skipped ${skippedCount} duplicate(s).`);
  };
  tx.onerror = () => {
    console.error("Failed to save uploaded file(s)", tx.error);
    alert("Could not save the uploaded file(s).");
  };
});

movieSearch.addEventListener("input", debounce(() => renderMovie(movieSearch.value)));

document.getElementById("btn-shuffle-movie").addEventListener("click", () => {
  shuffleArray(movie);
  saveListSortMode("movie", "shuffle", movie);
  renderMovie(movieSearch.value);
});

document.getElementById("btn-sort-az-movie").addEventListener("click", () => {
  movie.sort((a, b) => a.name.localeCompare(b.name));
  saveListSortMode("movie", "az", movie);
  renderMovie(movieSearch.value);
});

document.getElementById("btn-sort-za-movie").addEventListener("click", () => {
  movie.sort((a, b) => b.name.localeCompare(a.name));
  saveListSortMode("movie", "za", movie);
  renderMovie(movieSearch.value);
});

playPauseMovieBtn.addEventListener("click", () => {
  if (!currentMovieId && movie.length) return playMovieById(movie[0].id);
  if (moviePlayer.paused) {
    moviePlayer.play();
    playPauseMovieBtn.textContent = "Pause";
  } else {
    moviePlayer.pause();
    playPauseMovieBtn.textContent = "Play";
  }
});

nextMovieBtn.addEventListener("click", () => playNextMovie());

prevMovieBtn.addEventListener("click", () => playPrevMovie());

toggleRepeatMovieBtn.addEventListener("click", () => {
  movieRepeat = !movieRepeat;
  moviePlayer.loop = movieRepeat;
  toggleRepeatMovieBtn.textContent = `Repeat: ${movieRepeat ? "On" : "Off"}`;
});

moviePlayer.addEventListener("timeupdate", () => {
  if (!moviePlayer.duration) return;
  movieProgress.value = moviePlayer.currentTime / moviePlayer.duration * 100;
  updateRangeFill(movieProgress);
  movieCurrentTimeEl.textContent = formatTime(moviePlayer.currentTime);
  movieDurationEl.textContent = formatTime(moviePlayer.duration);
  if (currentMovieId !== null) {
    const now = Date.now();
    if (now - lastMoviePositionSave > POSITION_SAVE_INTERVAL) {
      lastMoviePositionSave = now;
      moviePositions[currentMovieId] = moviePlayer.currentTime;
      appSet("moviePositions", moviePositions);
    }
  }
});

movieProgress.addEventListener("input", () => {
  if (moviePlayer.duration) moviePlayer.currentTime = movieProgress.value / 100 * moviePlayer.duration;
  updateRangeFill(movieProgress);
});

moviePlayer.addEventListener("pause", () => {
  if (currentMovieId !== null && moviePlayer.duration) {
    moviePositions[currentMovieId] = moviePlayer.currentTime;
    appSet("moviePositions", moviePositions);
  }
});

moviePlayer.addEventListener("ended", () => {
  if (currentMovieId !== null) {
    delete moviePositions[currentMovieId];
    appSet("moviePositions", moviePositions);
  }
  playNextMovie();
});

document.getElementById("forward-10-movie").addEventListener("click", () => {
  moviePlayer.currentTime += 10;
});

document.getElementById("rewind-10-movie").addEventListener("click", () => {
  moviePlayer.currentTime = Math.max(0, moviePlayer.currentTime - 10);
});

function moviePlaylistCtx() {
  return {
    playlistsObj: moviePlaylists,
    metaObj: moviePlaylistMeta,
    mediaArray: () => movie,
    historyType: "movie",
    listEl: moviePlaylistsEl,
    toolbarEl: moviePlaylistToolbarEl,
    tracksEl: playlistMovie,
    headerEl: moviePlaylistHeaderEl,
    titleEl: moviePlaylistTitle,
    getCurrent: () => currentMoviePlaylist,
    setCurrent: v => {
      currentMoviePlaylist = v;
    },
    getSortMode: () => moviePlaylistSortMode,
    setSortMode: v => {
      moviePlaylistSortMode = v;
      appSet("moviePlaylistSortMode", v);
    },
    saveFn: saveMoviePlaylists,
    saveMetaFn: saveMoviePlaylistMeta,
    renderNamesFn: renderMoviePlaylists,
    renderTracksFn: renderPlaylistMovie,
    selectFn: selectMoviePlaylist,
    playByIdFn: id => playMovieById(id),
    currentPlayingId: () => currentMovieId,
    setPlaying: v => {
      moviePlaylistPlaying = v;
    }
  };
}

function renderMoviePlaylists() {
  renderPlaylistNamesGeneric(moviePlaylistCtx());
}

function selectMoviePlaylist(name) {
  currentMoviePlaylist = name;
  moviePlaylistTitle.textContent = isSmartPlaylist(name) ? smartPlaylistLabel(name) : name;
  renderPlaylistMovie();
  renderMoviePlaylists();
}

function renderPlaylistMovie() {
  renderPlaylistTracksGeneric(moviePlaylistCtx());
}

function saveMoviePlaylists() {
  appSet("moviePlaylists", moviePlaylists);
}

function saveMoviePlaylistMeta() {
  appSet("moviePlaylistMeta", moviePlaylistMeta);
}

document.getElementById("btn-create-movie-playlist").addEventListener("click", () => {
  const name = moviePlaylistName.value.trim();
  if (!name || moviePlaylists[name] || isSmartPlaylist(name)) return alert("Invalid or duplicate playlist name");
  moviePlaylists[name] = [];
  getPlaylistMeta(moviePlaylistMeta, name);
  moviePlaylistName.value = "";
  renderMoviePlaylists();
  saveMoviePlaylists();
  saveMoviePlaylistMeta();
});

document.getElementById("btn-delete-movie-playlist").addEventListener("click", () => {
  if (!currentMoviePlaylist || isSmartPlaylist(currentMoviePlaylist)) return alert("Select a playlist first");
  delete moviePlaylists[currentMoviePlaylist];
  delete moviePlaylistMeta[currentMoviePlaylist];
  currentMoviePlaylist = null;
  moviePlaylistTitle.textContent = "Select a playlist";
  renderPlaylistMovie();
  renderMoviePlaylists();
  saveMoviePlaylists();
  saveMoviePlaylistMeta();
});

document.getElementById("btn-add-selected-movie-to-playlist").addEventListener("click", () => {
  if (!currentMoviePlaylist || isSmartPlaylist(currentMoviePlaylist)) return alert("Select a playlist first");
  document.querySelectorAll("#movie-list input[type=checkbox]:checked").forEach(cb => {
    const id = Number(cb.dataset.id);
    if (!moviePlaylists[currentMoviePlaylist].includes(id)) moviePlaylists[currentMoviePlaylist].push(id);
  });
  touchPlaylistMeta(moviePlaylistMeta, currentMoviePlaylist);
  renderPlaylistMovie();
  renderMoviePlaylists();
  saveMoviePlaylists();
  saveMoviePlaylistMeta();
});

document.getElementById("btn-add-all-movie-to-playlist").addEventListener("click", () => {
  if (!currentMoviePlaylist || isSmartPlaylist(currentMoviePlaylist)) return alert("Select a playlist first");
  movie.forEach(item => {
    if (!moviePlaylists[currentMoviePlaylist].includes(item.id)) moviePlaylists[currentMoviePlaylist].push(item.id);
  });
  touchPlaylistMeta(moviePlaylistMeta, currentMoviePlaylist);
  renderPlaylistMovie();
  renderMoviePlaylists();
  saveMoviePlaylists();
  saveMoviePlaylistMeta();
});

document.getElementById("btn-remove-movie-from-playlist").addEventListener("click", () => {
  if (!currentMoviePlaylist || isSmartPlaylist(currentMoviePlaylist)) return;
  const toRemove = Array.from(playlistMovie.querySelectorAll("input[type=checkbox]:checked")).map(cb => Number(cb.dataset.id));
  moviePlaylists[currentMoviePlaylist] = moviePlaylists[currentMoviePlaylist].filter(id => !toRemove.includes(id));
  touchPlaylistMeta(moviePlaylistMeta, currentMoviePlaylist);
  renderPlaylistMovie();
  renderMoviePlaylists();
  saveMoviePlaylists();
  saveMoviePlaylistMeta();
});

document.getElementById("btn-clear-movie-playlist").addEventListener("click", () => {
  if (!currentMoviePlaylist || isSmartPlaylist(currentMoviePlaylist)) return;
  moviePlaylists[currentMoviePlaylist] = [];
  touchPlaylistMeta(moviePlaylistMeta, currentMoviePlaylist);
  renderPlaylistMovie();
  renderMoviePlaylists();
  saveMoviePlaylists();
  saveMoviePlaylistMeta();
});

document.getElementById("btn-play-movie-playlist").addEventListener("click", () => {
  const ids = getActivePlaylistIds(moviePlaylistCtx());
  if (!currentMoviePlaylist || !ids.length) return alert("Select a playlist with movies");
  moviePlaylistPlaying = true;
  playMovieById(ids[0]);
});

document.getElementById("btn-export-movie-playlist").addEventListener("click", () => {
  exportPlaylistFile(currentMoviePlaylist, currentMoviePlaylist ? getActivePlaylistIds(moviePlaylistCtx()) : null, movie);
});

document.getElementById("movie-playlist-import").addEventListener("change", async e => {
  const file = e.target.files[0];
  if (!file) return;
  try {
    await importPlaylistFile(file, movieDB, "movie", movie, moviePlaylists, saveMoviePlaylists, renderPlaylistMovie, renderMoviePlaylists, selectMoviePlaylist, moviePlaylistMeta, saveMoviePlaylistMeta, "video");
  } finally {
    e.target.value = "";
  }
  renderMovie(movieSearch.value);
});

PLAYLIST_FOLDER_IMPORT_HANDLERS["movie-playlist-import"] = async (files, folderName) => {
  await importPlaylistFolder(files, folderName, movieDB, "movie", movie, moviePlaylists, saveMoviePlaylists, renderPlaylistMovie, renderMoviePlaylists, selectMoviePlaylist, moviePlaylistMeta, saveMoviePlaylistMeta, "video");
  renderMovie(movieSearch.value);
};

(function enablePlaylistPanelDrop(wrapId, isValidId, getCurrentName, addToPlaylist, saveFn, renderListFn, renderNamesFn) {
  const wrap = document.getElementById(wrapId);
  if (!wrap) return;
  wrap.addEventListener("dragover", e => {
    if (!getCurrentName() || !e.dataTransfer.types.includes("text/plain")) return;
    e.preventDefault();
    e.dataTransfer.dropEffect = "copy";
    wrap.classList.add("drag-over");
  });
  wrap.addEventListener("dragleave", e => {
    if (!wrap.contains(e.relatedTarget)) wrap.classList.remove("drag-over");
  });
  wrap.addEventListener("drop", e => {
    e.preventDefault();
    wrap.classList.remove("drag-over");
    const name = getCurrentName();
    if (!name) return;
    const id = Number(e.dataTransfer.getData("text/plain"));
    if (!id || !isValidId(id)) return;
    addToPlaylist(name, id);
    saveFn();
    renderListFn();
    renderNamesFn();
  });
})("playlist-movie-wrap", id => !!movie.find(m => m.id === id), () => currentMoviePlaylist, (name, id) => {
  if (!moviePlaylists[name].includes(id)) moviePlaylists[name].push(id);
}, saveMoviePlaylists, renderPlaylistMovie, renderMoviePlaylists);

let comedy = [];

let currentComedyId = null;

let comedyPositions = {};

let comedyPlaylists = {};

let comedyPlaylistMeta = {};

let currentComedyPlaylist = null;

let comedyPlaylistPlaying = false;

let comedyLoopPlaylist = false;

let comedyPlaylistSortMode = "name";

let comedyRepeat = false;

let lastComedyPositionSave = 0;

let comedyDB;

const comedySearch = document.getElementById("comedy-search");

const comedyUpload = document.getElementById("comedy-upload");

const comedyList = document.getElementById("comedy-list");

const comedyCount = document.getElementById("comedy-count");

const currentComedyDisplay = document.getElementById("current-comedy");

const comedyPlayer = document.getElementById("comedy-player");

const comedyProgress = document.getElementById("comedy-progress");

const comedyCurrentTimeEl = document.getElementById("comedy-current-time");

const comedyDurationEl = document.getElementById("comedy-duration");

const playPauseComedyBtn = document.getElementById("play-pause-comedy");

const nextComedyBtn = document.getElementById("next-comedy");

const prevComedyBtn = document.getElementById("prev-comedy");

const toggleRepeatComedyBtn = document.getElementById("toggle-repeat-comedy");

const comedyVolume = document.getElementById("comedy-volume");

const comedyMuteBtn = document.getElementById("comedy-mute-btn");

const comedyVolumeLabel = document.getElementById("comedy-volume-label");

const comedySpeedGroup = document.getElementById("comedy-speed-group");

const comedyPlaylistsEl = document.getElementById("comedy-playlists");

const comedyPlaylistToolbarEl = document.getElementById("comedy-playlist-toolbar");

const comedyPlaylistName = document.getElementById("comedy-playlist-name");

const playlistComedy = document.getElementById("playlist-comedy");

const comedyPlaylistTitle = document.getElementById("comedy-playlist-title");

const comedyPlaylistHeaderEl = document.getElementById("comedy-playlist-header");

function openComedyDB() {
  return openTerminalDB("ComedyPlayerDB", [ {
    name: "comedy"
  } ]);
}

async function loadComedyFromDB() {
  if (!comedyDB || !currentUserId) {
    comedy.length = 0;
    renderComedy(comedySearch.value);
    return;
  }
  const rows = await loadUserRecordsIndexed(comedyDB, "comedy", currentUserId);
  comedy.length = 0;
  comedy.push(...rows);
  restoreListSortMode("comedy", comedy);
  renderComedy(comedySearch.value);
}

function renderComedy(filter = "") {
  const f = filter.toLowerCase();
  const visible = comedy.filter(item => !f || item.name.toLowerCase().includes(f));
  renderListBatched(comedyList, visible, item => {
    const li = document.createElement("li");
    if (item.id === currentComedyId) li.classList.add("selected");
    const name = document.createElement("span");
    name.textContent = item.name;
    const playBtn = document.createElement("button");
    playBtn.textContent = "▶";
    playBtn.className = "media-row-play-btn";
    playBtn.addEventListener("click", () => playComedyById(item.id));
    const deleteBtn = document.createElement("button");
    deleteBtn.textContent = "✕";
    deleteBtn.addEventListener("click", () => deleteComedyById(item.id));
    li.append(name, playBtn, deleteBtn);
    return li;
  });
  comedyCount.textContent = `Total Specials: ${comedy.length}`;
}

function playComedyById(id, isResume) {
  const item = comedy.find(v => v.id === id);
  if (!item) return;
  let url;
  try {
    url = URL.createObjectURL(item.blob);
  } catch (err) {
    console.error("Failed to create a playback URL", err);
    alert("Could not load this file for playback.");
    return;
  }
  currentComedyId = id;
  if (comedyPlayer.dataset.url) URL.revokeObjectURL(comedyPlayer.dataset.url);
  comedyPlayer.src = url;
  comedyPlayer.dataset.url = url;
  const resumeAt = comedyPositions[id];
  if (resumeAt) {
    const restorePosition = () => {
      if (resumeAt < comedyPlayer.duration - 2) comedyPlayer.currentTime = resumeAt;
      comedyPlayer.removeEventListener("loadedmetadata", restorePosition);
    };
    comedyPlayer.addEventListener("loadedmetadata", restorePosition);
  }
  currentComedyDisplay.textContent = item.name;
  comedyPlayer.play().then(() => {
    playPauseComedyBtn.textContent = "Pause";
  }).catch(err => {
    console.error("Playback failed to start", err);
    playPauseComedyBtn.textContent = "Play";
  });
  renderComedy(comedySearch.value);
}

function stopComedy() {
  currentComedyId = null;
  comedyPlayer.pause();
  comedyPlayer.removeAttribute("src");
  if (comedyPlayer.dataset.url) {
    URL.revokeObjectURL(comedyPlayer.dataset.url);
    delete comedyPlayer.dataset.url;
  }
  currentComedyDisplay.textContent = "No special selected";
  playPauseComedyBtn.textContent = "Play";
  renderComedy(comedySearch.value);
}

function playNextComedy() {
  const queuedId = consumeQueueNext("comedy");
  if (queuedId !== null) return playComedyById(queuedId);
  if (comedyPlaylistPlaying && currentComedyPlaylist) {
    const list = getActivePlaylistIds(comedyPlaylistCtx());
    const shuffle = !isSmartPlaylist(currentComedyPlaylist) && getPlaylistMeta(comedyPlaylistMeta, currentComedyPlaylist).shuffle;
    const next = pickNextInList(list, currentComedyId, shuffle);
    if (next !== null) return playComedyById(next);
    if (comedyLoopPlaylist && list.length) return playComedyById(shuffle ? list[Math.floor(Math.random() * list.length)] : list[0]);
    comedyPlaylistPlaying = false;
    return;
  }
  if (!comedy.length) return;
  const idx = comedy.findIndex(v => v.id === currentComedyId);
  const nextIdx = idx === -1 ? 0 : (idx + 1) % comedy.length;
  playComedyById(comedy[nextIdx].id);
}

function playPrevComedy() {
  if (comedyPlaylistPlaying && currentComedyPlaylist) {
    const list = getActivePlaylistIds(comedyPlaylistCtx());
    const idx = list.indexOf(currentComedyId);
    if (idx > 0) return playComedyById(list[idx - 1]);
    return;
  }
  if (!comedy.length) return;
  const idx = comedy.findIndex(v => v.id === currentComedyId);
  const prevIdx = idx <= 0 ? comedy.length - 1 : idx - 1;
  playComedyById(comedy[prevIdx].id);
}

function deleteComedyById(id) {
  if (!comedyDB) return;
  if (!confirm("Delete this item?")) return;
  const tx = comedyDB.transaction("comedy", "readwrite");
  tx.objectStore("comedy").delete(id);
  tx.oncomplete = () => {
    if (currentComedyId === id) stopComedy();
    delete comedyPositions[id];
    appSet("comedyPositions", comedyPositions);
    loadComedyFromDB();
  };
}

comedyUpload.addEventListener("change", async e => {
  if (!comedyDB || !currentUserId) return;
  const rawFiles = [ ...e.target.files ];
  if (!rawFiles.length) return;
  const files = filterUploadedMediaFiles(rawFiles, "video");
  if (!files.length) {
    comedyUpload.value = "";
    return;
  }
  const existingKeys = new Set(comedy.map(v => `${v.name.toLowerCase()}|${v.blob.size}`));
  const newFiles = files.filter(f => !existingKeys.has(`${f.name.toLowerCase()}|${f.size}`));
  const skippedCount = files.length - newFiles.length;
  if (!newFiles.length) {
    comedyUpload.value = "";
    if (skippedCount) alert(`Skipped ${skippedCount} duplicate file(s) already in your library.`);
    return;
  }
  const tx = comedyDB.transaction("comedy", "readwrite");
  const store = tx.objectStore("comedy");
  newFiles.forEach(file => {
    store.add({
      name: file.name,
      blob: file,
      userId: currentUserId
    });
  });
  tx.oncomplete = () => {
    comedyUpload.value = "";
    loadComedyFromDB();
    if (skippedCount) alert(`Added ${newFiles.length} file(s). Skipped ${skippedCount} duplicate(s).`);
  };
  tx.onerror = () => {
    console.error("Failed to save uploaded file(s)", tx.error);
    alert("Could not save the uploaded file(s).");
  };
});

comedySearch.addEventListener("input", debounce(() => renderComedy(comedySearch.value)));

document.getElementById("btn-shuffle-comedy").addEventListener("click", () => {
  shuffleArray(comedy);
  saveListSortMode("comedy", "shuffle", comedy);
  renderComedy(comedySearch.value);
});

document.getElementById("btn-sort-az-comedy").addEventListener("click", () => {
  comedy.sort((a, b) => a.name.localeCompare(b.name));
  saveListSortMode("comedy", "az", comedy);
  renderComedy(comedySearch.value);
});

document.getElementById("btn-sort-za-comedy").addEventListener("click", () => {
  comedy.sort((a, b) => b.name.localeCompare(a.name));
  saveListSortMode("comedy", "za", comedy);
  renderComedy(comedySearch.value);
});

playPauseComedyBtn.addEventListener("click", () => {
  if (!currentComedyId && comedy.length) return playComedyById(comedy[0].id);
  if (comedyPlayer.paused) {
    comedyPlayer.play();
    playPauseComedyBtn.textContent = "Pause";
  } else {
    comedyPlayer.pause();
    playPauseComedyBtn.textContent = "Play";
  }
});

nextComedyBtn.addEventListener("click", () => playNextComedy());

prevComedyBtn.addEventListener("click", () => playPrevComedy());

toggleRepeatComedyBtn.addEventListener("click", () => {
  comedyRepeat = !comedyRepeat;
  comedyPlayer.loop = comedyRepeat;
  toggleRepeatComedyBtn.textContent = `Repeat: ${comedyRepeat ? "On" : "Off"}`;
});

comedyPlayer.addEventListener("timeupdate", () => {
  if (!comedyPlayer.duration) return;
  comedyProgress.value = comedyPlayer.currentTime / comedyPlayer.duration * 100;
  updateRangeFill(comedyProgress);
  comedyCurrentTimeEl.textContent = formatTime(comedyPlayer.currentTime);
  comedyDurationEl.textContent = formatTime(comedyPlayer.duration);
  if (currentComedyId !== null) {
    const now = Date.now();
    if (now - lastComedyPositionSave > POSITION_SAVE_INTERVAL) {
      lastComedyPositionSave = now;
      comedyPositions[currentComedyId] = comedyPlayer.currentTime;
      appSet("comedyPositions", comedyPositions);
    }
  }
});

comedyProgress.addEventListener("input", () => {
  if (comedyPlayer.duration) comedyPlayer.currentTime = comedyProgress.value / 100 * comedyPlayer.duration;
  updateRangeFill(comedyProgress);
});

comedyPlayer.addEventListener("pause", () => {
  if (currentComedyId !== null && comedyPlayer.duration) {
    comedyPositions[currentComedyId] = comedyPlayer.currentTime;
    appSet("comedyPositions", comedyPositions);
  }
});

comedyPlayer.addEventListener("ended", () => {
  if (currentComedyId !== null) {
    delete comedyPositions[currentComedyId];
    appSet("comedyPositions", comedyPositions);
  }
  playNextComedy();
});

document.getElementById("forward-10-comedy").addEventListener("click", () => {
  comedyPlayer.currentTime += 10;
});

document.getElementById("rewind-10-comedy").addEventListener("click", () => {
  comedyPlayer.currentTime = Math.max(0, comedyPlayer.currentTime - 10);
});

function comedyPlaylistCtx() {
  return {
    playlistsObj: comedyPlaylists,
    metaObj: comedyPlaylistMeta,
    mediaArray: () => comedy,
    historyType: "comedy",
    listEl: comedyPlaylistsEl,
    toolbarEl: comedyPlaylistToolbarEl,
    tracksEl: playlistComedy,
    headerEl: comedyPlaylistHeaderEl,
    titleEl: comedyPlaylistTitle,
    getCurrent: () => currentComedyPlaylist,
    setCurrent: v => {
      currentComedyPlaylist = v;
    },
    getSortMode: () => comedyPlaylistSortMode,
    setSortMode: v => {
      comedyPlaylistSortMode = v;
      appSet("comedyPlaylistSortMode", v);
    },
    saveFn: saveComedyPlaylists,
    saveMetaFn: saveComedyPlaylistMeta,
    renderNamesFn: renderComedyPlaylists,
    renderTracksFn: renderPlaylistComedy,
    selectFn: selectComedyPlaylist,
    playByIdFn: id => playComedyById(id),
    currentPlayingId: () => currentComedyId,
    setPlaying: v => {
      comedyPlaylistPlaying = v;
    }
  };
}

function renderComedyPlaylists() {
  renderPlaylistNamesGeneric(comedyPlaylistCtx());
}

function selectComedyPlaylist(name) {
  currentComedyPlaylist = name;
  comedyPlaylistTitle.textContent = isSmartPlaylist(name) ? smartPlaylistLabel(name) : name;
  renderPlaylistComedy();
  renderComedyPlaylists();
}

function renderPlaylistComedy() {
  renderPlaylistTracksGeneric(comedyPlaylistCtx());
}

function saveComedyPlaylists() {
  appSet("comedyPlaylists", comedyPlaylists);
}

function saveComedyPlaylistMeta() {
  appSet("comedyPlaylistMeta", comedyPlaylistMeta);
}

document.getElementById("btn-create-comedy-playlist").addEventListener("click", () => {
  const name = comedyPlaylistName.value.trim();
  if (!name || comedyPlaylists[name] || isSmartPlaylist(name)) return alert("Invalid or duplicate playlist name");
  comedyPlaylists[name] = [];
  getPlaylistMeta(comedyPlaylistMeta, name);
  comedyPlaylistName.value = "";
  renderComedyPlaylists();
  saveComedyPlaylists();
  saveComedyPlaylistMeta();
});

document.getElementById("btn-delete-comedy-playlist").addEventListener("click", () => {
  if (!currentComedyPlaylist || isSmartPlaylist(currentComedyPlaylist)) return alert("Select a playlist first");
  delete comedyPlaylists[currentComedyPlaylist];
  delete comedyPlaylistMeta[currentComedyPlaylist];
  currentComedyPlaylist = null;
  comedyPlaylistTitle.textContent = "Select a playlist";
  renderPlaylistComedy();
  renderComedyPlaylists();
  saveComedyPlaylists();
  saveComedyPlaylistMeta();
});

document.getElementById("btn-add-selected-comedy-to-playlist").addEventListener("click", () => {
  if (!currentComedyPlaylist || isSmartPlaylist(currentComedyPlaylist)) return alert("Select a playlist first");
  document.querySelectorAll("#comedy-list input[type=checkbox]:checked").forEach(cb => {
    const id = Number(cb.dataset.id);
    if (!comedyPlaylists[currentComedyPlaylist].includes(id)) comedyPlaylists[currentComedyPlaylist].push(id);
  });
  touchPlaylistMeta(comedyPlaylistMeta, currentComedyPlaylist);
  renderPlaylistComedy();
  renderComedyPlaylists();
  saveComedyPlaylists();
  saveComedyPlaylistMeta();
});

document.getElementById("btn-add-all-comedy-to-playlist").addEventListener("click", () => {
  if (!currentComedyPlaylist || isSmartPlaylist(currentComedyPlaylist)) return alert("Select a playlist first");
  comedy.forEach(item => {
    if (!comedyPlaylists[currentComedyPlaylist].includes(item.id)) comedyPlaylists[currentComedyPlaylist].push(item.id);
  });
  touchPlaylistMeta(comedyPlaylistMeta, currentComedyPlaylist);
  renderPlaylistComedy();
  renderComedyPlaylists();
  saveComedyPlaylists();
  saveComedyPlaylistMeta();
});

document.getElementById("btn-remove-comedy-from-playlist").addEventListener("click", () => {
  if (!currentComedyPlaylist || isSmartPlaylist(currentComedyPlaylist)) return;
  const toRemove = Array.from(playlistComedy.querySelectorAll("input[type=checkbox]:checked")).map(cb => Number(cb.dataset.id));
  comedyPlaylists[currentComedyPlaylist] = comedyPlaylists[currentComedyPlaylist].filter(id => !toRemove.includes(id));
  touchPlaylistMeta(comedyPlaylistMeta, currentComedyPlaylist);
  renderPlaylistComedy();
  renderComedyPlaylists();
  saveComedyPlaylists();
  saveComedyPlaylistMeta();
});

document.getElementById("btn-clear-comedy-playlist").addEventListener("click", () => {
  if (!currentComedyPlaylist || isSmartPlaylist(currentComedyPlaylist)) return;
  comedyPlaylists[currentComedyPlaylist] = [];
  touchPlaylistMeta(comedyPlaylistMeta, currentComedyPlaylist);
  renderPlaylistComedy();
  renderComedyPlaylists();
  saveComedyPlaylists();
  saveComedyPlaylistMeta();
});

document.getElementById("btn-play-comedy-playlist").addEventListener("click", () => {
  const ids = getActivePlaylistIds(comedyPlaylistCtx());
  if (!currentComedyPlaylist || !ids.length) return alert("Select a playlist with comedys");
  comedyPlaylistPlaying = true;
  playComedyById(ids[0]);
});

document.getElementById("btn-export-comedy-playlist").addEventListener("click", () => {
  exportPlaylistFile(currentComedyPlaylist, currentComedyPlaylist ? getActivePlaylistIds(comedyPlaylistCtx()) : null, comedy);
});

document.getElementById("comedy-playlist-import").addEventListener("change", async e => {
  const file = e.target.files[0];
  if (!file) return;
  try {
    await importPlaylistFile(file, comedyDB, "comedy", comedy, comedyPlaylists, saveComedyPlaylists, renderPlaylistComedy, renderComedyPlaylists, selectComedyPlaylist, comedyPlaylistMeta, saveComedyPlaylistMeta, "video");
  } finally {
    e.target.value = "";
  }
  renderComedy(comedySearch.value);
});

PLAYLIST_FOLDER_IMPORT_HANDLERS["comedy-playlist-import"] = async (files, folderName) => {
  await importPlaylistFolder(files, folderName, comedyDB, "comedy", comedy, comedyPlaylists, saveComedyPlaylists, renderPlaylistComedy, renderComedyPlaylists, selectComedyPlaylist, comedyPlaylistMeta, saveComedyPlaylistMeta, "video");
  renderComedy(comedySearch.value);
};

(function enablePlaylistPanelDrop(wrapId, isValidId, getCurrentName, addToPlaylist, saveFn, renderListFn, renderNamesFn) {
  const wrap = document.getElementById(wrapId);
  if (!wrap) return;
  wrap.addEventListener("dragover", e => {
    if (!getCurrentName() || !e.dataTransfer.types.includes("text/plain")) return;
    e.preventDefault();
    e.dataTransfer.dropEffect = "copy";
    wrap.classList.add("drag-over");
  });
  wrap.addEventListener("dragleave", e => {
    if (!wrap.contains(e.relatedTarget)) wrap.classList.remove("drag-over");
  });
  wrap.addEventListener("drop", e => {
    e.preventDefault();
    wrap.classList.remove("drag-over");
    const name = getCurrentName();
    if (!name) return;
    const id = Number(e.dataTransfer.getData("text/plain"));
    if (!id || !isValidId(id)) return;
    addToPlaylist(name, id);
    saveFn();
    renderListFn();
    renderNamesFn();
  });
})("playlist-comedy-wrap", id => !!comedy.find(m => m.id === id), () => currentComedyPlaylist, (name, id) => {
  if (!comedyPlaylists[name].includes(id)) comedyPlaylists[name].push(id);
}, saveComedyPlaylists, renderPlaylistComedy, renderComedyPlaylists);

let webseries = [];

let currentWebSeriesId = null;

let webseriesPositions = {};

let webseriesPlaylists = {};

let webseriesPlaylistMeta = {};

let currentWebSeriesPlaylist = null;

let webseriesPlaylistPlaying = false;

let webseriesLoopPlaylist = false;

let webseriesPlaylistSortMode = "name";

let webseriesRepeat = false;

let lastWebSeriesPositionSave = 0;

let webseriesDB;

const webseriesSearch = document.getElementById("webseries-search");

const webseriesUpload = document.getElementById("webseries-upload");

const webseriesList = document.getElementById("webseries-list");

const webseriesCount = document.getElementById("webseries-count");

const currentWebSeriesDisplay = document.getElementById("current-webseries");

const webseriesPlayer = document.getElementById("webseries-player");

const webseriesProgress = document.getElementById("webseries-progress");

const webseriesCurrentTimeEl = document.getElementById("webseries-current-time");

const webseriesDurationEl = document.getElementById("webseries-duration");

const playPauseWebSeriesBtn = document.getElementById("play-pause-webseries");

const nextWebSeriesBtn = document.getElementById("next-webseries");

const prevWebSeriesBtn = document.getElementById("prev-webseries");

const toggleRepeatWebSeriesBtn = document.getElementById("toggle-repeat-webseries");

const webseriesVolume = document.getElementById("webseries-volume");

const webseriesMuteBtn = document.getElementById("webseries-mute-btn");

const webseriesVolumeLabel = document.getElementById("webseries-volume-label");

const webseriesSpeedGroup = document.getElementById("webseries-speed-group");

const webseriesPlaylistsEl = document.getElementById("webseries-playlists");

const webseriesPlaylistToolbarEl = document.getElementById("webseries-playlist-toolbar");

const webseriesPlaylistName = document.getElementById("webseries-playlist-name");

const playlistWebSeries = document.getElementById("playlist-webseries");

const webseriesPlaylistTitle = document.getElementById("webseries-playlist-title");

const webseriesPlaylistHeaderEl = document.getElementById("webseries-playlist-header");

function openWebSeriesDB() {
  return openTerminalDB("WebSeriesPlayerDB", [ {
    name: "webseries"
  } ]);
}

async function loadWebSeriesFromDB() {
  if (!webseriesDB || !currentUserId) {
    webseries.length = 0;
    renderWebSeries(webseriesSearch.value);
    return;
  }
  const rows = await loadUserRecordsIndexed(webseriesDB, "webseries", currentUserId);
  webseries.length = 0;
  webseries.push(...rows);
  restoreListSortMode("webseries", webseries);
  renderWebSeries(webseriesSearch.value);
}

function renderWebSeries(filter = "") {
  const f = filter.toLowerCase();
  const visible = webseries.filter(item => !f || item.name.toLowerCase().includes(f));
  renderListBatched(webseriesList, visible, item => {
    const li = document.createElement("li");
    if (item.id === currentWebSeriesId) li.classList.add("selected");
    const name = document.createElement("span");
    name.textContent = item.name;
    const playBtn = document.createElement("button");
    playBtn.textContent = "▶";
    playBtn.className = "media-row-play-btn";
    playBtn.addEventListener("click", () => playWebSeriesById(item.id));
    const deleteBtn = document.createElement("button");
    deleteBtn.textContent = "✕";
    deleteBtn.addEventListener("click", () => deleteWebSeriesById(item.id));
    li.append(name, playBtn, deleteBtn);
    return li;
  });
  webseriesCount.textContent = `Total Web Series: ${webseries.length}`;
}

function playWebSeriesById(id, isResume) {
  const item = webseries.find(v => v.id === id);
  if (!item) return;
  let url;
  try {
    url = URL.createObjectURL(item.blob);
  } catch (err) {
    console.error("Failed to create a playback URL", err);
    alert("Could not load this file for playback.");
    return;
  }
  currentWebSeriesId = id;
  if (webseriesPlayer.dataset.url) URL.revokeObjectURL(webseriesPlayer.dataset.url);
  webseriesPlayer.src = url;
  webseriesPlayer.dataset.url = url;
  const resumeAt = webseriesPositions[id];
  if (resumeAt) {
    const restorePosition = () => {
      if (resumeAt < webseriesPlayer.duration - 2) webseriesPlayer.currentTime = resumeAt;
      webseriesPlayer.removeEventListener("loadedmetadata", restorePosition);
    };
    webseriesPlayer.addEventListener("loadedmetadata", restorePosition);
  }
  currentWebSeriesDisplay.textContent = item.name;
  webseriesPlayer.play().then(() => {
    playPauseWebSeriesBtn.textContent = "Pause";
  }).catch(err => {
    console.error("Playback failed to start", err);
    playPauseWebSeriesBtn.textContent = "Play";
  });
  renderWebSeries(webseriesSearch.value);
}

function stopWebSeries() {
  currentWebSeriesId = null;
  webseriesPlayer.pause();
  webseriesPlayer.removeAttribute("src");
  if (webseriesPlayer.dataset.url) {
    URL.revokeObjectURL(webseriesPlayer.dataset.url);
    delete webseriesPlayer.dataset.url;
  }
  currentWebSeriesDisplay.textContent = "No web series selected";
  playPauseWebSeriesBtn.textContent = "Play";
  renderWebSeries(webseriesSearch.value);
}

function playNextWebSeries() {
  const queuedId = consumeQueueNext("webseries");
  if (queuedId !== null) return playWebSeriesById(queuedId);
  if (webseriesPlaylistPlaying && currentWebSeriesPlaylist) {
    const list = getActivePlaylistIds(webseriesPlaylistCtx());
    const shuffle = !isSmartPlaylist(currentWebSeriesPlaylist) && getPlaylistMeta(webseriesPlaylistMeta, currentWebSeriesPlaylist).shuffle;
    const next = pickNextInList(list, currentWebSeriesId, shuffle);
    if (next !== null) return playWebSeriesById(next);
    if (webseriesLoopPlaylist && list.length) return playWebSeriesById(shuffle ? list[Math.floor(Math.random() * list.length)] : list[0]);
    webseriesPlaylistPlaying = false;
    return;
  }
  if (!webseries.length) return;
  const idx = webseries.findIndex(v => v.id === currentWebSeriesId);
  const nextIdx = idx === -1 ? 0 : (idx + 1) % webseries.length;
  playWebSeriesById(webseries[nextIdx].id);
}

function playPrevWebSeries() {
  if (webseriesPlaylistPlaying && currentWebSeriesPlaylist) {
    const list = getActivePlaylistIds(webseriesPlaylistCtx());
    const idx = list.indexOf(currentWebSeriesId);
    if (idx > 0) return playWebSeriesById(list[idx - 1]);
    return;
  }
  if (!webseries.length) return;
  const idx = webseries.findIndex(v => v.id === currentWebSeriesId);
  const prevIdx = idx <= 0 ? webseries.length - 1 : idx - 1;
  playWebSeriesById(webseries[prevIdx].id);
}

function deleteWebSeriesById(id) {
  if (!webseriesDB) return;
  if (!confirm("Delete this item?")) return;
  const tx = webseriesDB.transaction("webseries", "readwrite");
  tx.objectStore("webseries").delete(id);
  tx.oncomplete = () => {
    if (currentWebSeriesId === id) stopWebSeries();
    delete webseriesPositions[id];
    appSet("webseriesPositions", webseriesPositions);
    loadWebSeriesFromDB();
  };
}

webseriesUpload.addEventListener("change", async e => {
  if (!webseriesDB || !currentUserId) return;
  const rawFiles = [ ...e.target.files ];
  if (!rawFiles.length) return;
  const files = filterUploadedMediaFiles(rawFiles, "video");
  if (!files.length) {
    webseriesUpload.value = "";
    return;
  }
  const existingKeys = new Set(webseries.map(v => `${v.name.toLowerCase()}|${v.blob.size}`));
  const newFiles = files.filter(f => !existingKeys.has(`${f.name.toLowerCase()}|${f.size}`));
  const skippedCount = files.length - newFiles.length;
  if (!newFiles.length) {
    webseriesUpload.value = "";
    if (skippedCount) alert(`Skipped ${skippedCount} duplicate file(s) already in your library.`);
    return;
  }
  const tx = webseriesDB.transaction("webseries", "readwrite");
  const store = tx.objectStore("webseries");
  newFiles.forEach(file => {
    store.add({
      name: file.name,
      blob: file,
      userId: currentUserId
    });
  });
  tx.oncomplete = () => {
    webseriesUpload.value = "";
    loadWebSeriesFromDB();
    if (skippedCount) alert(`Added ${newFiles.length} file(s). Skipped ${skippedCount} duplicate(s).`);
  };
  tx.onerror = () => {
    console.error("Failed to save uploaded file(s)", tx.error);
    alert("Could not save the uploaded file(s).");
  };
});

webseriesSearch.addEventListener("input", debounce(() => renderWebSeries(webseriesSearch.value)));

document.getElementById("btn-shuffle-webseries").addEventListener("click", () => {
  shuffleArray(webseries);
  saveListSortMode("webseries", "shuffle", webseries);
  renderWebSeries(webseriesSearch.value);
});

document.getElementById("btn-sort-az-webseries").addEventListener("click", () => {
  webseries.sort((a, b) => a.name.localeCompare(b.name));
  saveListSortMode("webseries", "az", webseries);
  renderWebSeries(webseriesSearch.value);
});

document.getElementById("btn-sort-za-webseries").addEventListener("click", () => {
  webseries.sort((a, b) => b.name.localeCompare(a.name));
  saveListSortMode("webseries", "za", webseries);
  renderWebSeries(webseriesSearch.value);
});

playPauseWebSeriesBtn.addEventListener("click", () => {
  if (!currentWebSeriesId && webseries.length) return playWebSeriesById(webseries[0].id);
  if (webseriesPlayer.paused) {
    webseriesPlayer.play();
    playPauseWebSeriesBtn.textContent = "Pause";
  } else {
    webseriesPlayer.pause();
    playPauseWebSeriesBtn.textContent = "Play";
  }
});

nextWebSeriesBtn.addEventListener("click", () => playNextWebSeries());

prevWebSeriesBtn.addEventListener("click", () => playPrevWebSeries());

toggleRepeatWebSeriesBtn.addEventListener("click", () => {
  webseriesRepeat = !webseriesRepeat;
  webseriesPlayer.loop = webseriesRepeat;
  toggleRepeatWebSeriesBtn.textContent = `Repeat: ${webseriesRepeat ? "On" : "Off"}`;
});

webseriesPlayer.addEventListener("timeupdate", () => {
  if (!webseriesPlayer.duration) return;
  webseriesProgress.value = webseriesPlayer.currentTime / webseriesPlayer.duration * 100;
  updateRangeFill(webseriesProgress);
  webseriesCurrentTimeEl.textContent = formatTime(webseriesPlayer.currentTime);
  webseriesDurationEl.textContent = formatTime(webseriesPlayer.duration);
  if (currentWebSeriesId !== null) {
    const now = Date.now();
    if (now - lastWebSeriesPositionSave > POSITION_SAVE_INTERVAL) {
      lastWebSeriesPositionSave = now;
      webseriesPositions[currentWebSeriesId] = webseriesPlayer.currentTime;
      appSet("webseriesPositions", webseriesPositions);
    }
  }
});

webseriesProgress.addEventListener("input", () => {
  if (webseriesPlayer.duration) webseriesPlayer.currentTime = webseriesProgress.value / 100 * webseriesPlayer.duration;
  updateRangeFill(webseriesProgress);
});

webseriesPlayer.addEventListener("pause", () => {
  if (currentWebSeriesId !== null && webseriesPlayer.duration) {
    webseriesPositions[currentWebSeriesId] = webseriesPlayer.currentTime;
    appSet("webseriesPositions", webseriesPositions);
  }
});

webseriesPlayer.addEventListener("ended", () => {
  if (currentWebSeriesId !== null) {
    delete webseriesPositions[currentWebSeriesId];
    appSet("webseriesPositions", webseriesPositions);
  }
  playNextWebSeries();
});

document.getElementById("forward-10-webseries").addEventListener("click", () => {
  webseriesPlayer.currentTime += 10;
});

document.getElementById("rewind-10-webseries").addEventListener("click", () => {
  webseriesPlayer.currentTime = Math.max(0, webseriesPlayer.currentTime - 10);
});

function webseriesPlaylistCtx() {
  return {
    playlistsObj: webseriesPlaylists,
    metaObj: webseriesPlaylistMeta,
    mediaArray: () => webseries,
    historyType: "webseries",
    listEl: webseriesPlaylistsEl,
    toolbarEl: webseriesPlaylistToolbarEl,
    tracksEl: playlistWebSeries,
    headerEl: webseriesPlaylistHeaderEl,
    titleEl: webseriesPlaylistTitle,
    getCurrent: () => currentWebSeriesPlaylist,
    setCurrent: v => {
      currentWebSeriesPlaylist = v;
    },
    getSortMode: () => webseriesPlaylistSortMode,
    setSortMode: v => {
      webseriesPlaylistSortMode = v;
      appSet("webseriesPlaylistSortMode", v);
    },
    saveFn: saveWebSeriesPlaylists,
    saveMetaFn: saveWebSeriesPlaylistMeta,
    renderNamesFn: renderWebSeriesPlaylists,
    renderTracksFn: renderPlaylistWebSeries,
    selectFn: selectWebSeriesPlaylist,
    playByIdFn: id => playWebSeriesById(id),
    currentPlayingId: () => currentWebSeriesId,
    setPlaying: v => {
      webseriesPlaylistPlaying = v;
    }
  };
}

function renderWebSeriesPlaylists() {
  renderPlaylistNamesGeneric(webseriesPlaylistCtx());
}

function selectWebSeriesPlaylist(name) {
  currentWebSeriesPlaylist = name;
  webseriesPlaylistTitle.textContent = isSmartPlaylist(name) ? smartPlaylistLabel(name) : name;
  renderPlaylistWebSeries();
  renderWebSeriesPlaylists();
}

function renderPlaylistWebSeries() {
  renderPlaylistTracksGeneric(webseriesPlaylistCtx());
}

function saveWebSeriesPlaylists() {
  appSet("webseriesPlaylists", webseriesPlaylists);
}

function saveWebSeriesPlaylistMeta() {
  appSet("webseriesPlaylistMeta", webseriesPlaylistMeta);
}

document.getElementById("btn-create-webseries-playlist").addEventListener("click", () => {
  const name = webseriesPlaylistName.value.trim();
  if (!name || webseriesPlaylists[name] || isSmartPlaylist(name)) return alert("Invalid or duplicate playlist name");
  webseriesPlaylists[name] = [];
  getPlaylistMeta(webseriesPlaylistMeta, name);
  webseriesPlaylistName.value = "";
  renderWebSeriesPlaylists();
  saveWebSeriesPlaylists();
  saveWebSeriesPlaylistMeta();
});

document.getElementById("btn-delete-webseries-playlist").addEventListener("click", () => {
  if (!currentWebSeriesPlaylist || isSmartPlaylist(currentWebSeriesPlaylist)) return alert("Select a playlist first");
  delete webseriesPlaylists[currentWebSeriesPlaylist];
  delete webseriesPlaylistMeta[currentWebSeriesPlaylist];
  currentWebSeriesPlaylist = null;
  webseriesPlaylistTitle.textContent = "Select a playlist";
  renderPlaylistWebSeries();
  renderWebSeriesPlaylists();
  saveWebSeriesPlaylists();
  saveWebSeriesPlaylistMeta();
});

document.getElementById("btn-add-selected-webseries-to-playlist").addEventListener("click", () => {
  if (!currentWebSeriesPlaylist || isSmartPlaylist(currentWebSeriesPlaylist)) return alert("Select a playlist first");
  document.querySelectorAll("#webseries-list input[type=checkbox]:checked").forEach(cb => {
    const id = Number(cb.dataset.id);
    if (!webseriesPlaylists[currentWebSeriesPlaylist].includes(id)) webseriesPlaylists[currentWebSeriesPlaylist].push(id);
  });
  touchPlaylistMeta(webseriesPlaylistMeta, currentWebSeriesPlaylist);
  renderPlaylistWebSeries();
  renderWebSeriesPlaylists();
  saveWebSeriesPlaylists();
  saveWebSeriesPlaylistMeta();
});

document.getElementById("btn-add-all-webseries-to-playlist").addEventListener("click", () => {
  if (!currentWebSeriesPlaylist || isSmartPlaylist(currentWebSeriesPlaylist)) return alert("Select a playlist first");
  webseries.forEach(item => {
    if (!webseriesPlaylists[currentWebSeriesPlaylist].includes(item.id)) webseriesPlaylists[currentWebSeriesPlaylist].push(item.id);
  });
  touchPlaylistMeta(webseriesPlaylistMeta, currentWebSeriesPlaylist);
  renderPlaylistWebSeries();
  renderWebSeriesPlaylists();
  saveWebSeriesPlaylists();
  saveWebSeriesPlaylistMeta();
});

document.getElementById("btn-remove-webseries-from-playlist").addEventListener("click", () => {
  if (!currentWebSeriesPlaylist || isSmartPlaylist(currentWebSeriesPlaylist)) return;
  const toRemove = Array.from(playlistWebSeries.querySelectorAll("input[type=checkbox]:checked")).map(cb => Number(cb.dataset.id));
  webseriesPlaylists[currentWebSeriesPlaylist] = webseriesPlaylists[currentWebSeriesPlaylist].filter(id => !toRemove.includes(id));
  touchPlaylistMeta(webseriesPlaylistMeta, currentWebSeriesPlaylist);
  renderPlaylistWebSeries();
  renderWebSeriesPlaylists();
  saveWebSeriesPlaylists();
  saveWebSeriesPlaylistMeta();
});

document.getElementById("btn-clear-webseries-playlist").addEventListener("click", () => {
  if (!currentWebSeriesPlaylist || isSmartPlaylist(currentWebSeriesPlaylist)) return;
  webseriesPlaylists[currentWebSeriesPlaylist] = [];
  touchPlaylistMeta(webseriesPlaylistMeta, currentWebSeriesPlaylist);
  renderPlaylistWebSeries();
  renderWebSeriesPlaylists();
  saveWebSeriesPlaylists();
  saveWebSeriesPlaylistMeta();
});

document.getElementById("btn-play-webseries-playlist").addEventListener("click", () => {
  const ids = getActivePlaylistIds(webseriesPlaylistCtx());
  if (!currentWebSeriesPlaylist || !ids.length) return alert("Select a playlist with web series");
  webseriesPlaylistPlaying = true;
  playWebSeriesById(ids[0]);
});

document.getElementById("btn-export-webseries-playlist").addEventListener("click", () => {
  exportPlaylistFile(currentWebSeriesPlaylist, currentWebSeriesPlaylist ? getActivePlaylistIds(webseriesPlaylistCtx()) : null, webseries);
});

document.getElementById("webseries-playlist-import").addEventListener("change", async e => {
  const file = e.target.files[0];
  if (!file) return;
  try {
    await importPlaylistFile(file, webseriesDB, "webseries", webseries, webseriesPlaylists, saveWebSeriesPlaylists, renderPlaylistWebSeries, renderWebSeriesPlaylists, selectWebSeriesPlaylist, webseriesPlaylistMeta, saveWebSeriesPlaylistMeta, "video");
  } finally {
    e.target.value = "";
  }
  renderWebSeries(webseriesSearch.value);
});

PLAYLIST_FOLDER_IMPORT_HANDLERS["webseries-playlist-import"] = async (files, folderName) => {
  await importPlaylistFolder(files, folderName, webseriesDB, "webseries", webseries, webseriesPlaylists, saveWebSeriesPlaylists, renderPlaylistWebSeries, renderWebSeriesPlaylists, selectWebSeriesPlaylist, webseriesPlaylistMeta, saveWebSeriesPlaylistMeta, "video");
  renderWebSeries(webseriesSearch.value);
};

(function enablePlaylistPanelDrop(wrapId, isValidId, getCurrentName, addToPlaylist, saveFn, renderListFn, renderNamesFn) {
  const wrap = document.getElementById(wrapId);
  if (!wrap) return;
  wrap.addEventListener("dragover", e => {
    if (!getCurrentName() || !e.dataTransfer.types.includes("text/plain")) return;
    e.preventDefault();
    e.dataTransfer.dropEffect = "copy";
    wrap.classList.add("drag-over");
  });
  wrap.addEventListener("dragleave", e => {
    if (!wrap.contains(e.relatedTarget)) wrap.classList.remove("drag-over");
  });
  wrap.addEventListener("drop", e => {
    e.preventDefault();
    wrap.classList.remove("drag-over");
    const name = getCurrentName();
    if (!name) return;
    const id = Number(e.dataTransfer.getData("text/plain"));
    if (!id || !isValidId(id)) return;
    addToPlaylist(name, id);
    saveFn();
    renderListFn();
    renderNamesFn();
  });
})("playlist-webseries-wrap", id => !!webseries.find(w => w.id === id), () => currentWebSeriesPlaylist, (name, id) => {
  if (!webseriesPlaylists[name].includes(id)) webseriesPlaylists[name].push(id);
}, saveWebSeriesPlaylists, renderPlaylistWebSeries, renderWebSeriesPlaylists);

let games = [];

let currentGameId = null;

let gamesDB;

const gamesSearch = document.getElementById("games-search");

const gamesUpload = document.getElementById("games-upload");

const gamesList = document.getElementById("games-list");

const gamesCount = document.getElementById("games-count");

const currentGameDisplay = document.getElementById("current-game");

const gameFrame = document.getElementById("game-frame");

let gamesPlaylists = {};

let gamesPlaylistMeta = {};

let currentGamesPlaylist = null;

let gamesPlaylistSortMode = "name";

const gamesPlaylistsEl = document.getElementById("games-playlists");

const gamesPlaylistToolbarEl = document.getElementById("games-playlist-toolbar");

const gamesPlaylistName = document.getElementById("games-playlist-name");

const playlistGames = document.getElementById("playlist-games");

const gamesPlaylistTitle = document.getElementById("games-playlist-title");

const gamesPlaylistHeaderEl = document.getElementById("games-playlist-header");

function openGamesDB() {
  return openTerminalDB("GamesPlayerDB", [ {
    name: "games"
  } ]);
}

async function loadGamesFromDB() {
  if (!gamesDB || !currentUserId) {
    games.length = 0;
    renderGames(gamesSearch.value);
    return;
  }
  const rows = await loadUserRecordsIndexed(gamesDB, "games", currentUserId);
  games.length = 0;
  games.push(...rows);
  renderGames(gamesSearch.value);
}

function renderGames(filter = "") {
  const f = filter.toLowerCase();
  const visible = games.filter(game => !f || game.name.toLowerCase().includes(f));
  renderListBatched(gamesList, visible, game => {
    const li = document.createElement("li");
    if (game.id === currentGameId) li.classList.add("selected");
    const name = document.createElement("span");
    name.textContent = game.name;
    const playBtn = document.createElement("button");
    playBtn.textContent = "▶";
    playBtn.className = "media-row-play-btn";
    playBtn.addEventListener("click", () => playGameById(game.id));
    const deleteBtn = document.createElement("button");
    deleteBtn.textContent = "✕";
    deleteBtn.addEventListener("click", () => deleteGameById(game.id));
    li.append(name, playBtn, deleteBtn);
    return li;
  });
  gamesCount.textContent = `Total Games: ${games.length}`;
}

function playGameById(id) {
  const game = games.find(g => g.id === id);
  if (!game) return;
  let url;
  try {
    url = URL.createObjectURL(game.blob);
  } catch (err) {
    console.error("Failed to load this game", err);
    alert("Could not load this game.");
    return;
  }
  currentGameId = id;
  if (gameFrame.dataset.url) URL.revokeObjectURL(gameFrame.dataset.url);
  gameFrame.src = url;
  gameFrame.dataset.url = url;
  currentGameDisplay.textContent = game.name;
  renderGames(gamesSearch.value);
}

function stopGame() {
  currentGameId = null;
  if (gameFrame.dataset.url) {
    URL.revokeObjectURL(gameFrame.dataset.url);
    delete gameFrame.dataset.url;
  }
  gameFrame.removeAttribute("src");
  currentGameDisplay.textContent = "No game selected";
  renderGames(gamesSearch.value);
}

function deleteGameById(id) {
  if (!gamesDB) return;
  if (!confirm("Delete this game?")) return;
  const tx = gamesDB.transaction("games", "readwrite");
  tx.objectStore("games").delete(id);
  tx.oncomplete = () => {
    if (currentGameId === id) stopGame();
    loadGamesFromDB();
  };
}

function gameBaseName(fileName) {
  return fileName.replace(/\.(html?|css|js)$/i, "");
}

function gameFileKind(fileName) {
  const ext = (fileName.split(".").pop() || "").toLowerCase();
  if (ext === "html" || ext === "htm") return "html";
  if (ext === "css") return "css";
  if (ext === "js") return "js";
  return null;
}

async function buildCombinedGameBlob(group) {
  let htmlText = group.html ? await group.html.text() : "<!DOCTYPE html><html><head></head><body></body></html>";
  const cssText = group.css ? await group.css.text() : "";
  const jsText = group.js ? await group.js.text() : "";
  if (cssText) {
    const styleTag = `<style>\n${cssText}\n</style>`;
    if (/<\/head>/i.test(htmlText)) {
      htmlText = htmlText.replace(/<\/head>/i, `${styleTag}\n</head>`);
    } else {
      htmlText = styleTag + htmlText;
    }
  }
  if (jsText) {
    const scriptTag = `<script>\n${jsText}\n<\/script>`;
    if (/<\/body>/i.test(htmlText)) {
      htmlText = htmlText.replace(/<\/body>/i, `${scriptTag}\n</body>`);
    } else {
      htmlText += scriptTag;
    }
  }
  return new Blob([ htmlText ], {
    type: "text/html"
  });
}

gamesUpload.addEventListener("change", async e => {
  if (!gamesDB || !currentUserId) return;
  const rawFiles = [ ...e.target.files ];
  if (!rawFiles.length) return;
  const files = filterUploadedMediaFiles(rawFiles, "game");
  if (!files.length) {
    gamesUpload.value = "";
    return;
  }
  const groups = new Map;
  const standalone = [];
  files.forEach(file => {
    const kind = gameFileKind(file.name);
    if (!kind) return;
    if (kind === "css" || kind === "js") {
      const base = gameBaseName(file.name);
      if (!groups.has(base)) groups.set(base, {});
      groups.get(base)[kind] = file;
    } else {
      standalone.push(file);
    }
  });
  standalone.forEach(file => {
    const base = gameBaseName(file.name);
    if (!groups.has(base)) groups.set(base, {});
    groups.get(base).html = file;
  });
  const entries = [];
  for (const [base, group] of groups) {
    if (!group.html && !group.css && !group.js) continue;
    const isCombined = !!(group.css || group.js);
    const blob = group.html && !isCombined ? group.html : await buildCombinedGameBlob(group);
    const name = group.html ? group.html.name : `${base}.html`;
    entries.push({
      name: name,
      blob: blob
    });
  }
  if (!entries.length) {
    gamesUpload.value = "";
    return;
  }
  const existingKeys = new Set(games.map(g => `${g.name.toLowerCase()}|${g.blob.size}`));
  const newEntries = entries.filter(en => !existingKeys.has(`${en.name.toLowerCase()}|${en.blob.size}`));
  const skippedCount = entries.length - newEntries.length;
  if (!newEntries.length) {
    gamesUpload.value = "";
    if (skippedCount) alert(`Skipped ${skippedCount} duplicate game(s) already in your library.`);
    return;
  }
  const tx = gamesDB.transaction("games", "readwrite");
  const store = tx.objectStore("games");
  newEntries.forEach(entry => {
    store.add({
      name: entry.name,
      blob: entry.blob,
      userId: currentUserId
    });
  });
  tx.oncomplete = () => {
    gamesUpload.value = "";
    loadGamesFromDB();
    if (skippedCount) alert(`Added ${newEntries.length} game(s). Skipped ${skippedCount} duplicate(s).`);
  };
  tx.onerror = () => {
    console.error("Failed to save uploaded game(s)", tx.error);
    alert("Could not save the uploaded game file(s).");
  };
});

gamesSearch.addEventListener("input", debounce(() => renderGames(gamesSearch.value)));

document.getElementById("btn-stop-game").addEventListener("click", stopGame);

document.getElementById("btn-fullscreen-game").addEventListener("click", () => {
  if (gameFrame.requestFullscreen) gameFrame.requestFullscreen();
});

function gamesPlaylistCtx() {
  return {
    playlistsObj: gamesPlaylists,
    metaObj: gamesPlaylistMeta,
    mediaArray: () => games,
    historyType: "games",
    listEl: gamesPlaylistsEl,
    toolbarEl: gamesPlaylistToolbarEl,
    tracksEl: playlistGames,
    headerEl: gamesPlaylistHeaderEl,
    titleEl: gamesPlaylistTitle,
    getCurrent: () => currentGamesPlaylist,
    setCurrent: v => {
      currentGamesPlaylist = v;
    },
    getSortMode: () => gamesPlaylistSortMode,
    setSortMode: v => {
      gamesPlaylistSortMode = v;
      appSet("gamesPlaylistSortMode", v);
    },
    saveFn: saveGamesPlaylists,
    saveMetaFn: saveGamesPlaylistMeta,
    renderNamesFn: renderGamesPlaylists,
    renderTracksFn: renderPlaylistGames,
    selectFn: selectGamesPlaylist,
    playByIdFn: id => playGameById(id),
    currentPlayingId: () => currentGameId,
    setPlaying: () => {}
  };
}

function renderGamesPlaylists() {
  renderPlaylistNamesGeneric(gamesPlaylistCtx());
}

function selectGamesPlaylist(name) {
  currentGamesPlaylist = name;
  gamesPlaylistTitle.textContent = isSmartPlaylist(name) ? smartPlaylistLabel(name) : name;
  renderPlaylistGames();
  renderGamesPlaylists();
}

function renderPlaylistGames() {
  renderPlaylistTracksGeneric(gamesPlaylistCtx());
}

function saveGamesPlaylists() {
  appSet("gamesPlaylists", gamesPlaylists);
}

function saveGamesPlaylistMeta() {
  appSet("gamesPlaylistMeta", gamesPlaylistMeta);
}

document.getElementById("btn-create-games-playlist").addEventListener("click", () => {
  const name = gamesPlaylistName.value.trim();
  if (!name || gamesPlaylists[name] || isSmartPlaylist(name)) return alert("Invalid or duplicate playlist name");
  gamesPlaylists[name] = [];
  getPlaylistMeta(gamesPlaylistMeta, name);
  gamesPlaylistName.value = "";
  renderGamesPlaylists();
  saveGamesPlaylists();
  saveGamesPlaylistMeta();
});

document.getElementById("btn-delete-games-playlist").addEventListener("click", () => {
  if (!currentGamesPlaylist || isSmartPlaylist(currentGamesPlaylist)) return alert("Select a playlist first");
  delete gamesPlaylists[currentGamesPlaylist];
  delete gamesPlaylistMeta[currentGamesPlaylist];
  currentGamesPlaylist = null;
  gamesPlaylistTitle.textContent = "Select a playlist";
  renderPlaylistGames();
  renderGamesPlaylists();
  saveGamesPlaylists();
  saveGamesPlaylistMeta();
});

document.getElementById("btn-add-selected-games-to-playlist").addEventListener("click", () => {
  if (!currentGamesPlaylist || isSmartPlaylist(currentGamesPlaylist)) return alert("Select a playlist first");
  document.querySelectorAll("#games-list input[type=checkbox]:checked").forEach(cb => {
    const id = Number(cb.dataset.id);
    if (!gamesPlaylists[currentGamesPlaylist].includes(id)) gamesPlaylists[currentGamesPlaylist].push(id);
  });
  touchPlaylistMeta(gamesPlaylistMeta, currentGamesPlaylist);
  renderPlaylistGames();
  renderGamesPlaylists();
  saveGamesPlaylists();
  saveGamesPlaylistMeta();
});

document.getElementById("btn-add-all-games-to-playlist").addEventListener("click", () => {
  if (!currentGamesPlaylist || isSmartPlaylist(currentGamesPlaylist)) return alert("Select a playlist first");
  games.forEach(g => {
    if (!gamesPlaylists[currentGamesPlaylist].includes(g.id)) gamesPlaylists[currentGamesPlaylist].push(g.id);
  });
  touchPlaylistMeta(gamesPlaylistMeta, currentGamesPlaylist);
  renderPlaylistGames();
  renderGamesPlaylists();
  saveGamesPlaylists();
  saveGamesPlaylistMeta();
});

document.getElementById("btn-remove-games-from-playlist").addEventListener("click", () => {
  if (!currentGamesPlaylist || isSmartPlaylist(currentGamesPlaylist)) return;
  const toRemove = Array.from(playlistGames.querySelectorAll("input[type=checkbox]:checked")).map(cb => Number(cb.dataset.id));
  gamesPlaylists[currentGamesPlaylist] = gamesPlaylists[currentGamesPlaylist].filter(id => !toRemove.includes(id));
  touchPlaylistMeta(gamesPlaylistMeta, currentGamesPlaylist);
  renderPlaylistGames();
  renderGamesPlaylists();
  saveGamesPlaylists();
  saveGamesPlaylistMeta();
});

document.getElementById("btn-clear-games-playlist").addEventListener("click", () => {
  if (!currentGamesPlaylist || isSmartPlaylist(currentGamesPlaylist)) return;
  gamesPlaylists[currentGamesPlaylist] = [];
  touchPlaylistMeta(gamesPlaylistMeta, currentGamesPlaylist);
  renderPlaylistGames();
  renderGamesPlaylists();
  saveGamesPlaylists();
  saveGamesPlaylistMeta();
});

document.getElementById("btn-play-games-playlist").addEventListener("click", () => {
  const ids = getActivePlaylistIds(gamesPlaylistCtx());
  if (!currentGamesPlaylist || !ids.length) return alert("Select a playlist with games");
  playGameById(ids[0]);
});

document.getElementById("btn-export-games-playlist").addEventListener("click", () => {
  exportPlaylistFile(currentGamesPlaylist, currentGamesPlaylist ? getActivePlaylistIds(gamesPlaylistCtx()) : null, games);
});

document.getElementById("games-playlist-import").addEventListener("change", async e => {
  const file = e.target.files[0];
  if (!file) return;
  try {
    await importPlaylistFile(file, gamesDB, "games", games, gamesPlaylists, saveGamesPlaylists, renderPlaylistGames, renderGamesPlaylists, selectGamesPlaylist, gamesPlaylistMeta, saveGamesPlaylistMeta, "game");
  } finally {
    e.target.value = "";
  }
  renderGames(gamesSearch.value);
});

PLAYLIST_FOLDER_IMPORT_HANDLERS["games-playlist-import"] = async (files, folderName) => {
  await importPlaylistFolder(files, folderName, gamesDB, "games", games, gamesPlaylists, saveGamesPlaylists, renderPlaylistGames, renderGamesPlaylists, selectGamesPlaylist, gamesPlaylistMeta, saveGamesPlaylistMeta, "game");
  renderGames(gamesSearch.value);
};

(function enablePlaylistPanelDrop(wrapId, isValidId, getCurrentName, addToPlaylist, saveFn, renderListFn, renderNamesFn) {
  const wrap = document.getElementById(wrapId);
  if (!wrap) return;
  wrap.addEventListener("dragover", e => {
    if (!getCurrentName() || !e.dataTransfer.types.includes("text/plain")) return;
    e.preventDefault();
    e.dataTransfer.dropEffect = "copy";
    wrap.classList.add("drag-over");
  });
  wrap.addEventListener("dragleave", e => {
    if (!wrap.contains(e.relatedTarget)) wrap.classList.remove("drag-over");
  });
  wrap.addEventListener("drop", e => {
    e.preventDefault();
    wrap.classList.remove("drag-over");
    const name = getCurrentName();
    if (!name) return;
    const id = Number(e.dataTransfer.getData("text/plain"));
    if (!id || !isValidId(id)) return;
    addToPlaylist(name, id);
    saveFn();
    renderListFn();
    renderNamesFn();
  });
})("playlist-games-wrap", id => !!games.find(g => g.id === id), () => currentGamesPlaylist, (name, id) => {
  if (!gamesPlaylists[name].includes(id)) gamesPlaylists[name].push(id);
}, saveGamesPlaylists, renderPlaylistGames, renderGamesPlaylists);

let books = [];

let currentBookId = null;

let booksDB;

const booksSearch = document.getElementById("books-search");

const booksUpload = document.getElementById("books-upload");

const booksList = document.getElementById("books-list");

const booksCount = document.getElementById("books-count");

const currentBookDisplay = document.getElementById("current-book");

const bookFrame = document.getElementById("book-frame");

let booksPlaylists = {};

let booksPlaylistMeta = {};

let currentBooksPlaylist = null;

let booksPlaylistSortMode = "name";

const booksPlaylistsEl = document.getElementById("books-playlists");

const booksPlaylistToolbarEl = document.getElementById("books-playlist-toolbar");

const booksPlaylistName = document.getElementById("books-playlist-name");

const playlistBooks = document.getElementById("playlist-books");

const booksPlaylistTitle = document.getElementById("books-playlist-title");

const booksPlaylistHeaderEl = document.getElementById("books-playlist-header");

function openBooksDB() {
  return openTerminalDB("BooksPlayerDB", [ {
    name: "books"
  } ]);
}

async function loadBooksFromDB() {
  if (!booksDB || !currentUserId) {
    books.length = 0;
    renderBooks(booksSearch.value);
    return;
  }
  const rows = await loadUserRecordsIndexed(booksDB, "books", currentUserId);
  books.length = 0;
  books.push(...rows);
  renderBooks(booksSearch.value);
}

function renderBooks(filter = "") {
  const f = filter.toLowerCase();
  const visible = books.filter(book => !f || book.name.toLowerCase().includes(f));
  renderListBatched(booksList, visible, book => {
    const li = document.createElement("li");
    if (book.id === currentBookId) li.classList.add("selected");
    const name = document.createElement("span");
    name.textContent = book.name;
    const viewBtn = document.createElement("button");
    viewBtn.textContent = "▶";
    viewBtn.className = "media-row-play-btn";
    viewBtn.addEventListener("click", () => viewBookById(book.id));
    const deleteBtn = document.createElement("button");
    deleteBtn.textContent = "✕";
    deleteBtn.addEventListener("click", () => deleteBookById(book.id));
    li.append(name, viewBtn, deleteBtn);
    return li;
  });
  booksCount.textContent = `Total Books: ${books.length}`;
}

function viewBookById(id) {
  const book = books.find(b => b.id === id);
  if (!book) return;
  let url;
  try {
    url = URL.createObjectURL(book.blob);
  } catch (err) {
    console.error("Failed to load this book", err);
    alert("Could not load this book.");
    return;
  }
  currentBookId = id;
  if (bookFrame.dataset.url) URL.revokeObjectURL(bookFrame.dataset.url);
  bookFrame.src = url;
  bookFrame.dataset.url = url;
  currentBookDisplay.textContent = book.name;
  renderBooks(booksSearch.value);
}

function closeBook() {
  currentBookId = null;
  if (bookFrame.dataset.url) {
    URL.revokeObjectURL(bookFrame.dataset.url);
    delete bookFrame.dataset.url;
  }
  bookFrame.removeAttribute("src");
  currentBookDisplay.textContent = "No book selected";
  renderBooks(booksSearch.value);
}

function deleteBookById(id) {
  if (!booksDB) return;
  if (!confirm("Delete this book?")) return;
  const tx = booksDB.transaction("books", "readwrite");
  tx.objectStore("books").delete(id);
  tx.oncomplete = () => {
    if (currentBookId === id) closeBook();
    loadBooksFromDB();
  };
}

booksUpload.addEventListener("change", async e => {
  if (!booksDB || !currentUserId) return;
  const rawFiles = [ ...e.target.files ];
  if (!rawFiles.length) return;
  const files = filterUploadedMediaFiles(rawFiles, "pdf");
  if (!files.length) {
    booksUpload.value = "";
    return;
  }
  const existingKeys = new Set(books.map(b => `${b.name.toLowerCase()}|${b.blob.size}`));
  const newFiles = files.filter(f => !existingKeys.has(`${f.name.toLowerCase()}|${f.size}`));
  const skippedCount = files.length - newFiles.length;
  if (!newFiles.length) {
    booksUpload.value = "";
    if (skippedCount) alert(`Skipped ${skippedCount} duplicate book(s) already in your library.`);
    return;
  }
  const tx = booksDB.transaction("books", "readwrite");
  const store = tx.objectStore("books");
  newFiles.forEach(file => {
    store.add({
      name: file.name,
      blob: file,
      userId: currentUserId
    });
  });
  tx.oncomplete = () => {
    booksUpload.value = "";
    loadBooksFromDB();
    if (skippedCount) alert(`Added ${newFiles.length} book(s). Skipped ${skippedCount} duplicate(s).`);
  };
  tx.onerror = () => {
    console.error("Failed to save uploaded book(s)", tx.error);
    alert("Could not save the uploaded book file(s).");
  };
});

booksSearch.addEventListener("input", debounce(() => renderBooks(booksSearch.value)));

document.getElementById("btn-close-book").addEventListener("click", closeBook);

document.getElementById("btn-fullscreen-book").addEventListener("click", () => {
  if (bookFrame.requestFullscreen) bookFrame.requestFullscreen();
});

function booksPlaylistCtx() {
  return {
    playlistsObj: booksPlaylists,
    metaObj: booksPlaylistMeta,
    mediaArray: () => books,
    historyType: "books",
    listEl: booksPlaylistsEl,
    toolbarEl: booksPlaylistToolbarEl,
    tracksEl: playlistBooks,
    headerEl: booksPlaylistHeaderEl,
    titleEl: booksPlaylistTitle,
    getCurrent: () => currentBooksPlaylist,
    setCurrent: v => {
      currentBooksPlaylist = v;
    },
    getSortMode: () => booksPlaylistSortMode,
    setSortMode: v => {
      booksPlaylistSortMode = v;
      appSet("booksPlaylistSortMode", v);
    },
    saveFn: saveBooksPlaylists,
    saveMetaFn: saveBooksPlaylistMeta,
    renderNamesFn: renderBooksPlaylists,
    renderTracksFn: renderPlaylistBooks,
    selectFn: selectBooksPlaylist,
    playByIdFn: id => viewBookById(id),
    currentPlayingId: () => currentBookId,
    setPlaying: () => {}
  };
}

function renderBooksPlaylists() {
  renderPlaylistNamesGeneric(booksPlaylistCtx());
}

function selectBooksPlaylist(name) {
  currentBooksPlaylist = name;
  booksPlaylistTitle.textContent = isSmartPlaylist(name) ? smartPlaylistLabel(name) : name;
  renderPlaylistBooks();
  renderBooksPlaylists();
}

function renderPlaylistBooks() {
  renderPlaylistTracksGeneric(booksPlaylistCtx());
}

function saveBooksPlaylists() {
  appSet("booksPlaylists", booksPlaylists);
}

function saveBooksPlaylistMeta() {
  appSet("booksPlaylistMeta", booksPlaylistMeta);
}

document.getElementById("btn-create-books-playlist").addEventListener("click", () => {
  const name = booksPlaylistName.value.trim();
  if (!name || booksPlaylists[name] || isSmartPlaylist(name)) return alert("Invalid or duplicate playlist name");
  booksPlaylists[name] = [];
  getPlaylistMeta(booksPlaylistMeta, name);
  booksPlaylistName.value = "";
  renderBooksPlaylists();
  saveBooksPlaylists();
  saveBooksPlaylistMeta();
});

document.getElementById("btn-delete-books-playlist").addEventListener("click", () => {
  if (!currentBooksPlaylist || isSmartPlaylist(currentBooksPlaylist)) return alert("Select a playlist first");
  delete booksPlaylists[currentBooksPlaylist];
  delete booksPlaylistMeta[currentBooksPlaylist];
  currentBooksPlaylist = null;
  booksPlaylistTitle.textContent = "Select a playlist";
  renderPlaylistBooks();
  renderBooksPlaylists();
  saveBooksPlaylists();
  saveBooksPlaylistMeta();
});

document.getElementById("btn-add-selected-books-to-playlist").addEventListener("click", () => {
  if (!currentBooksPlaylist || isSmartPlaylist(currentBooksPlaylist)) return alert("Select a playlist first");
  document.querySelectorAll("#books-list input[type=checkbox]:checked").forEach(cb => {
    const id = Number(cb.dataset.id);
    if (!booksPlaylists[currentBooksPlaylist].includes(id)) booksPlaylists[currentBooksPlaylist].push(id);
  });
  touchPlaylistMeta(booksPlaylistMeta, currentBooksPlaylist);
  renderPlaylistBooks();
  renderBooksPlaylists();
  saveBooksPlaylists();
  saveBooksPlaylistMeta();
});

document.getElementById("btn-add-all-books-to-playlist").addEventListener("click", () => {
  if (!currentBooksPlaylist || isSmartPlaylist(currentBooksPlaylist)) return alert("Select a playlist first");
  books.forEach(b => {
    if (!booksPlaylists[currentBooksPlaylist].includes(b.id)) booksPlaylists[currentBooksPlaylist].push(b.id);
  });
  touchPlaylistMeta(booksPlaylistMeta, currentBooksPlaylist);
  renderPlaylistBooks();
  renderBooksPlaylists();
  saveBooksPlaylists();
  saveBooksPlaylistMeta();
});

document.getElementById("btn-remove-books-from-playlist").addEventListener("click", () => {
  if (!currentBooksPlaylist || isSmartPlaylist(currentBooksPlaylist)) return;
  const toRemove = Array.from(playlistBooks.querySelectorAll("input[type=checkbox]:checked")).map(cb => Number(cb.dataset.id));
  booksPlaylists[currentBooksPlaylist] = booksPlaylists[currentBooksPlaylist].filter(id => !toRemove.includes(id));
  touchPlaylistMeta(booksPlaylistMeta, currentBooksPlaylist);
  renderPlaylistBooks();
  renderBooksPlaylists();
  saveBooksPlaylists();
  saveBooksPlaylistMeta();
});

document.getElementById("btn-clear-books-playlist").addEventListener("click", () => {
  if (!currentBooksPlaylist || isSmartPlaylist(currentBooksPlaylist)) return;
  booksPlaylists[currentBooksPlaylist] = [];
  touchPlaylistMeta(booksPlaylistMeta, currentBooksPlaylist);
  renderPlaylistBooks();
  renderBooksPlaylists();
  saveBooksPlaylists();
  saveBooksPlaylistMeta();
});

document.getElementById("btn-play-books-playlist").addEventListener("click", () => {
  const ids = getActivePlaylistIds(booksPlaylistCtx());
  if (!currentBooksPlaylist || !ids.length) return alert("Select a playlist with books");
  viewBookById(ids[0]);
});

document.getElementById("btn-export-books-playlist").addEventListener("click", () => {
  exportPlaylistFile(currentBooksPlaylist, currentBooksPlaylist ? getActivePlaylistIds(booksPlaylistCtx()) : null, books);
});

document.getElementById("books-playlist-import").addEventListener("change", async e => {
  const file = e.target.files[0];
  if (!file) return;
  try {
    await importPlaylistFile(file, booksDB, "books", books, booksPlaylists, saveBooksPlaylists, renderPlaylistBooks, renderBooksPlaylists, selectBooksPlaylist, booksPlaylistMeta, saveBooksPlaylistMeta, "pdf");
  } finally {
    e.target.value = "";
  }
  renderBooks(booksSearch.value);
});

PLAYLIST_FOLDER_IMPORT_HANDLERS["books-playlist-import"] = async (files, folderName) => {
  await importPlaylistFolder(files, folderName, booksDB, "books", books, booksPlaylists, saveBooksPlaylists, renderPlaylistBooks, renderBooksPlaylists, selectBooksPlaylist, booksPlaylistMeta, saveBooksPlaylistMeta, "pdf");
  renderBooks(booksSearch.value);
};

(function enablePlaylistPanelDrop(wrapId, isValidId, getCurrentName, addToPlaylist, saveFn, renderListFn, renderNamesFn) {
  const wrap = document.getElementById(wrapId);
  if (!wrap) return;
  wrap.addEventListener("dragover", e => {
    if (!getCurrentName() || !e.dataTransfer.types.includes("text/plain")) return;
    e.preventDefault();
    e.dataTransfer.dropEffect = "copy";
    wrap.classList.add("drag-over");
  });
  wrap.addEventListener("dragleave", e => {
    if (!wrap.contains(e.relatedTarget)) wrap.classList.remove("drag-over");
  });
  wrap.addEventListener("drop", e => {
    e.preventDefault();
    wrap.classList.remove("drag-over");
    const name = getCurrentName();
    if (!name) return;
    const id = Number(e.dataTransfer.getData("text/plain"));
    if (!id || !isValidId(id)) return;
    addToPlaylist(name, id);
    saveFn();
    renderListFn();
    renderNamesFn();
  });
})("playlist-books-wrap", id => !!books.find(b => b.id === id), () => currentBooksPlaylist, (name, id) => {
  if (!booksPlaylists[name].includes(id)) booksPlaylists[name].push(id);
}, saveBooksPlaylists, renderPlaylistBooks, renderBooksPlaylists);

let gamevideo = [];

let currentGameVideoId = null;

let gamevideoPositions = {};

let gamevideoPlaylists = {};

let gamevideoPlaylistMeta = {};

let currentGameVideoPlaylist = null;

let gamevideoPlaylistPlaying = false;

let gamevideoLoopPlaylist = false;

let gamevideoPlaylistSortMode = "name";

let gamevideoRepeat = false;

let lastGameVideoPositionSave = 0;

let gamevideoDB;

const gamevideoSearch = document.getElementById("gamevideo-search");

const gamevideoUpload = document.getElementById("gamevideo-upload");

const gamevideoList = document.getElementById("gamevideo-list");

const gamevideoCount = document.getElementById("gamevideo-count");

const currentGameVideoDisplay = document.getElementById("current-gamevideo");

const gamevideoPlayer = document.getElementById("gamevideo-player");

const gamevideoProgress = document.getElementById("gamevideo-progress");

const gamevideoCurrentTimeEl = document.getElementById("gamevideo-current-time");

const gamevideoDurationEl = document.getElementById("gamevideo-duration");

const playPauseGameVideoBtn = document.getElementById("play-pause-gamevideo");

const nextGameVideoBtn = document.getElementById("next-gamevideo");

const prevGameVideoBtn = document.getElementById("prev-gamevideo");

const toggleRepeatGameVideoBtn = document.getElementById("toggle-repeat-gamevideo");

const gamevideoVolume = document.getElementById("gamevideo-volume");

const gamevideoMuteBtn = document.getElementById("gamevideo-mute-btn");

const gamevideoVolumeLabel = document.getElementById("gamevideo-volume-label");

const gamevideoSpeedGroup = document.getElementById("gamevideo-speed-group");

const gamevideoPlaylistsEl = document.getElementById("gamevideo-playlists");

const gamevideoPlaylistToolbarEl = document.getElementById("gamevideo-playlist-toolbar");

const gamevideoPlaylistName = document.getElementById("gamevideo-playlist-name");

const playlistGameVideo = document.getElementById("playlist-gamevideo");

const gamevideoPlaylistTitle = document.getElementById("gamevideo-playlist-title");

const gamevideoPlaylistHeaderEl = document.getElementById("gamevideo-playlist-header");

const selectAllGameVideoCheckbox = document.getElementById("select-all-gamevideo");

const deleteSelectedGameVideoBtn = document.getElementById("btn-delete-selected-gamevideo");

function openGameVideoDB() {
  return openTerminalDB("GameVideoPlayerDB", [ {
    name: "gamevideo"
  } ]);
}

async function loadGameVideoFromDB() {
  if (!gamevideoDB || !currentUserId) {
    gamevideo.length = 0;
    renderGameVideo(gamevideoSearch.value);
    return;
  }
  const rows = await loadUserRecordsIndexed(gamevideoDB, "gamevideo", currentUserId);
  gamevideo.length = 0;
  gamevideo.push(...rows);
  restoreListSortMode("gamevideo", gamevideo);
  renderGameVideo(gamevideoSearch.value);
}

function renderGameVideo(filter = "") {
  const f = filter.toLowerCase();
  const visible = gamevideo.filter(item => !f || item.name.toLowerCase().includes(f));
  renderListBatched(gamevideoList, visible, item => {
    const li = document.createElement("li");
    if (item.id === currentGameVideoId) li.classList.add("selected");
    const cb = document.createElement("input");
    cb.type = "checkbox";
    cb.dataset.id = item.id;
    cb.addEventListener("change", () => {
      li.classList.toggle("selected", cb.checked);
      const allChecked = Array.from(document.querySelectorAll("#gamevideo-list input[type=checkbox]")).every(c => c.checked);
      if (selectAllGameVideoCheckbox) selectAllGameVideoCheckbox.checked = allChecked;
    });
    const name = document.createElement("span");
    name.textContent = item.name;
    const playBtn = document.createElement("button");
    playBtn.textContent = "▶";
    playBtn.className = "media-row-play-btn";
    playBtn.addEventListener("click", () => playGameVideoById(item.id));
    const deleteBtn = document.createElement("button");
    deleteBtn.textContent = "✕";
    deleteBtn.addEventListener("click", () => deleteGameVideoById(item.id));
    li.append(cb, name, playBtn, deleteBtn);
    attachRowClickToggle(li, cb, playBtn);
    return li;
  });
  gamevideoCount.textContent = `Total Game Videos: ${gamevideo.length}`;
}

function playGameVideoById(id, isResume) {
  const item = gamevideo.find(v => v.id === id);
  if (!item) return;
  let url;
  try {
    url = URL.createObjectURL(item.blob);
  } catch (err) {
    console.error("Failed to create a playback URL", err);
    alert("Could not load this file for playback.");
    return;
  }
  currentGameVideoId = id;
  if (gamevideoPlayer.dataset.url) URL.revokeObjectURL(gamevideoPlayer.dataset.url);
  gamevideoPlayer.src = url;
  gamevideoPlayer.dataset.url = url;
  const resumeAt = gamevideoPositions[id];
  if (resumeAt) {
    const restorePosition = () => {
      if (resumeAt < gamevideoPlayer.duration - 2) gamevideoPlayer.currentTime = resumeAt;
      gamevideoPlayer.removeEventListener("loadedmetadata", restorePosition);
    };
    gamevideoPlayer.addEventListener("loadedmetadata", restorePosition);
  }
  currentGameVideoDisplay.textContent = item.name;
  gamevideoPlayer.play().then(() => {
    playPauseGameVideoBtn.textContent = "Pause";
  }).catch(err => {
    console.error("Playback failed to start", err);
    playPauseGameVideoBtn.textContent = "Play";
  });
  renderGameVideo(gamevideoSearch.value);
}

function stopGameVideo() {
  currentGameVideoId = null;
  gamevideoPlayer.pause();
  gamevideoPlayer.removeAttribute("src");
  if (gamevideoPlayer.dataset.url) {
    URL.revokeObjectURL(gamevideoPlayer.dataset.url);
    delete gamevideoPlayer.dataset.url;
  }
  currentGameVideoDisplay.textContent = "No game video selected";
  playPauseGameVideoBtn.textContent = "Play";
  renderGameVideo(gamevideoSearch.value);
}

function playNextGameVideo() {
  const queuedId = consumeQueueNext("gamevideo");
  if (queuedId !== null) return playGameVideoById(queuedId);
  if (gamevideoPlaylistPlaying && currentGameVideoPlaylist) {
    const list = getActivePlaylistIds(gamevideoPlaylistCtx());
    const shuffle = !isSmartPlaylist(currentGameVideoPlaylist) && getPlaylistMeta(gamevideoPlaylistMeta, currentGameVideoPlaylist).shuffle;
    const next = pickNextInList(list, currentGameVideoId, shuffle);
    if (next !== null) return playGameVideoById(next);
    if (gamevideoLoopPlaylist && list.length) return playGameVideoById(shuffle ? list[Math.floor(Math.random() * list.length)] : list[0]);
    gamevideoPlaylistPlaying = false;
    return;
  }
  if (!gamevideo.length) return;
  const idx = gamevideo.findIndex(v => v.id === currentGameVideoId);
  const nextIdx = idx === -1 ? 0 : (idx + 1) % gamevideo.length;
  playGameVideoById(gamevideo[nextIdx].id);
}

function playPrevGameVideo() {
  if (gamevideoPlaylistPlaying && currentGameVideoPlaylist) {
    const list = getActivePlaylistIds(gamevideoPlaylistCtx());
    const idx = list.indexOf(currentGameVideoId);
    if (idx > 0) return playGameVideoById(list[idx - 1]);
    return;
  }
  if (!gamevideo.length) return;
  const idx = gamevideo.findIndex(v => v.id === currentGameVideoId);
  const prevIdx = idx <= 0 ? gamevideo.length - 1 : idx - 1;
  playGameVideoById(gamevideo[prevIdx].id);
}

function deleteGameVideoById(id) {
  if (!gamevideoDB) return;
  if (!confirm("Delete this item?")) return;
  const tx = gamevideoDB.transaction("gamevideo", "readwrite");
  tx.objectStore("gamevideo").delete(id);
  tx.oncomplete = () => {
    if (currentGameVideoId === id) stopGameVideo();
    delete gamevideoPositions[id];
    appSet("gamevideoPositions", gamevideoPositions);
    loadGameVideoFromDB();
  };
}

if (selectAllGameVideoCheckbox) {
  selectAllGameVideoCheckbox.addEventListener("change", () => {
    const checked = selectAllGameVideoCheckbox.checked;
    gamevideoList.querySelectorAll("li").forEach(li => {
      const cb = li.querySelector("input[type=checkbox]");
      if (!cb) return;
      cb.checked = checked;
      li.classList.toggle("selected", checked);
    });
  });
}

if (deleteSelectedGameVideoBtn) {
  deleteSelectedGameVideoBtn.addEventListener("click", () => {
    if (!gamevideoDB) return alert("Database not ready");
    const selected = document.querySelectorAll("#gamevideo-list input[type=checkbox]:checked");
    if (selected.length === 0) return alert("No items selected");
    if (!confirm("Delete selected items?")) return;
    const idsToRemove = Array.from(selected).map(cb => Number(cb.dataset.id)).filter(id => !isNaN(id));
    const tx = gamevideoDB.transaction("gamevideo", "readwrite");
    const store = tx.objectStore("gamevideo");
    idsToRemove.forEach(id => store.delete(id));
    tx.oncomplete = () => {
      if (idsToRemove.includes(currentGameVideoId)) stopGameVideo();
      idsToRemove.forEach(id => delete gamevideoPositions[id]);
      appSet("gamevideoPositions", gamevideoPositions);
      mediaQueues.gamevideo = mediaQueues.gamevideo.filter(id => !idsToRemove.includes(id));
      saveQueue("gamevideo");
      renderQueue("gamevideo");
      selectAllGameVideoCheckbox.checked = false;
      loadGameVideoFromDB();
    };
  });
}

gamevideoUpload.addEventListener("change", async e => {
  if (!gamevideoDB || !currentUserId) return;
  const rawFiles = [ ...e.target.files ];
  if (!rawFiles.length) return;
  const files = filterUploadedMediaFiles(rawFiles, "video");
  if (!files.length) {
    gamevideoUpload.value = "";
    return;
  }
  const existingKeys = new Set(gamevideo.map(v => `${v.name.toLowerCase()}|${v.blob.size}`));
  const newFiles = files.filter(f => !existingKeys.has(`${f.name.toLowerCase()}|${f.size}`));
  const skippedCount = files.length - newFiles.length;
  if (!newFiles.length) {
    gamevideoUpload.value = "";
    if (skippedCount) alert(`Skipped ${skippedCount} duplicate file(s) already in your library.`);
    return;
  }
  const tx = gamevideoDB.transaction("gamevideo", "readwrite");
  const store = tx.objectStore("gamevideo");
  newFiles.forEach(file => {
    store.add({
      name: file.name,
      blob: file,
      userId: currentUserId
    });
  });
  tx.oncomplete = () => {
    gamevideoUpload.value = "";
    loadGameVideoFromDB();
    if (skippedCount) alert(`Added ${newFiles.length} file(s). Skipped ${skippedCount} duplicate(s).`);
  };
  tx.onerror = () => {
    console.error("Failed to save uploaded file(s)", tx.error);
    alert("Could not save the uploaded file(s).");
  };
});

gamevideoSearch.addEventListener("input", debounce(() => renderGameVideo(gamevideoSearch.value)));

document.getElementById("btn-shuffle-gamevideo").addEventListener("click", () => {
  shuffleArray(gamevideo);
  saveListSortMode("gamevideo", "shuffle", gamevideo);
  renderGameVideo(gamevideoSearch.value);
});

document.getElementById("btn-sort-az-gamevideo").addEventListener("click", () => {
  gamevideo.sort((a, b) => a.name.localeCompare(b.name));
  saveListSortMode("gamevideo", "az", gamevideo);
  renderGameVideo(gamevideoSearch.value);
});

document.getElementById("btn-sort-za-gamevideo").addEventListener("click", () => {
  gamevideo.sort((a, b) => b.name.localeCompare(a.name));
  saveListSortMode("gamevideo", "za", gamevideo);
  renderGameVideo(gamevideoSearch.value);
});

playPauseGameVideoBtn.addEventListener("click", () => {
  if (!currentGameVideoId && gamevideo.length) return playGameVideoById(gamevideo[0].id);
  if (gamevideoPlayer.paused) {
    gamevideoPlayer.play();
    playPauseGameVideoBtn.textContent = "Pause";
  } else {
    gamevideoPlayer.pause();
    playPauseGameVideoBtn.textContent = "Play";
  }
});

nextGameVideoBtn.addEventListener("click", () => playNextGameVideo());

prevGameVideoBtn.addEventListener("click", () => playPrevGameVideo());

toggleRepeatGameVideoBtn.addEventListener("click", () => {
  gamevideoRepeat = !gamevideoRepeat;
  gamevideoPlayer.loop = gamevideoRepeat;
  toggleRepeatGameVideoBtn.textContent = `Repeat: ${gamevideoRepeat ? "On" : "Off"}`;
});

gamevideoPlayer.addEventListener("timeupdate", () => {
  if (!gamevideoPlayer.duration) return;
  gamevideoProgress.value = gamevideoPlayer.currentTime / gamevideoPlayer.duration * 100;
  updateRangeFill(gamevideoProgress);
  gamevideoCurrentTimeEl.textContent = formatTime(gamevideoPlayer.currentTime);
  gamevideoDurationEl.textContent = formatTime(gamevideoPlayer.duration);
  if (currentGameVideoId !== null) {
    const now = Date.now();
    if (now - lastGameVideoPositionSave > POSITION_SAVE_INTERVAL) {
      lastGameVideoPositionSave = now;
      gamevideoPositions[currentGameVideoId] = gamevideoPlayer.currentTime;
      appSet("gamevideoPositions", gamevideoPositions);
    }
  }
});

gamevideoProgress.addEventListener("input", () => {
  if (gamevideoPlayer.duration) gamevideoPlayer.currentTime = gamevideoProgress.value / 100 * gamevideoPlayer.duration;
  updateRangeFill(gamevideoProgress);
});

gamevideoPlayer.addEventListener("pause", () => {
  if (currentGameVideoId !== null && gamevideoPlayer.duration) {
    gamevideoPositions[currentGameVideoId] = gamevideoPlayer.currentTime;
    appSet("gamevideoPositions", gamevideoPositions);
  }
});

gamevideoPlayer.addEventListener("ended", () => {
  if (currentGameVideoId !== null) {
    delete gamevideoPositions[currentGameVideoId];
    appSet("gamevideoPositions", gamevideoPositions);
  }
  playNextGameVideo();
});

document.getElementById("forward-10-gamevideo").addEventListener("click", () => {
  gamevideoPlayer.currentTime += 10;
});

document.getElementById("rewind-10-gamevideo").addEventListener("click", () => {
  gamevideoPlayer.currentTime = Math.max(0, gamevideoPlayer.currentTime - 10);
});

function gamevideoPlaylistCtx() {
  return {
    playlistsObj: gamevideoPlaylists,
    metaObj: gamevideoPlaylistMeta,
    mediaArray: () => gamevideo,
    historyType: "gamevideo",
    listEl: gamevideoPlaylistsEl,
    toolbarEl: gamevideoPlaylistToolbarEl,
    tracksEl: playlistGameVideo,
    headerEl: gamevideoPlaylistHeaderEl,
    titleEl: gamevideoPlaylistTitle,
    getCurrent: () => currentGameVideoPlaylist,
    setCurrent: v => {
      currentGameVideoPlaylist = v;
    },
    getSortMode: () => gamevideoPlaylistSortMode,
    setSortMode: v => {
      gamevideoPlaylistSortMode = v;
      appSet("gamevideoPlaylistSortMode", v);
    },
    saveFn: saveGameVideoPlaylists,
    saveMetaFn: saveGameVideoPlaylistMeta,
    renderNamesFn: renderGameVideoPlaylists,
    renderTracksFn: renderPlaylistGameVideo,
    selectFn: selectGameVideoPlaylist,
    playByIdFn: id => playGameVideoById(id),
    currentPlayingId: () => currentGameVideoId,
    setPlaying: v => {
      gamevideoPlaylistPlaying = v;
    }
  };
}

function renderGameVideoPlaylists() {
  renderPlaylistNamesGeneric(gamevideoPlaylistCtx());
}

function selectGameVideoPlaylist(name) {
  currentGameVideoPlaylist = name;
  gamevideoPlaylistTitle.textContent = isSmartPlaylist(name) ? smartPlaylistLabel(name) : name;
  renderPlaylistGameVideo();
  renderGameVideoPlaylists();
}

function renderPlaylistGameVideo() {
  renderPlaylistTracksGeneric(gamevideoPlaylistCtx());
}

function saveGameVideoPlaylists() {
  appSet("gamevideoPlaylists", gamevideoPlaylists);
}

function saveGameVideoPlaylistMeta() {
  appSet("gamevideoPlaylistMeta", gamevideoPlaylistMeta);
}

document.getElementById("btn-create-gamevideo-playlist").addEventListener("click", () => {
  const name = gamevideoPlaylistName.value.trim();
  if (!name || gamevideoPlaylists[name] || isSmartPlaylist(name)) return alert("Invalid or duplicate playlist name");
  gamevideoPlaylists[name] = [];
  getPlaylistMeta(gamevideoPlaylistMeta, name);
  gamevideoPlaylistName.value = "";
  renderGameVideoPlaylists();
  saveGameVideoPlaylists();
  saveGameVideoPlaylistMeta();
});

document.getElementById("btn-delete-gamevideo-playlist").addEventListener("click", () => {
  if (!currentGameVideoPlaylist || isSmartPlaylist(currentGameVideoPlaylist)) return alert("Select a playlist first");
  delete gamevideoPlaylists[currentGameVideoPlaylist];
  delete gamevideoPlaylistMeta[currentGameVideoPlaylist];
  currentGameVideoPlaylist = null;
  gamevideoPlaylistTitle.textContent = "Select a playlist";
  renderPlaylistGameVideo();
  renderGameVideoPlaylists();
  saveGameVideoPlaylists();
  saveGameVideoPlaylistMeta();
});

document.getElementById("btn-add-selected-gamevideo-to-playlist").addEventListener("click", () => {
  if (!currentGameVideoPlaylist || isSmartPlaylist(currentGameVideoPlaylist)) return alert("Select a playlist first");
  document.querySelectorAll("#gamevideo-list input[type=checkbox]:checked").forEach(cb => {
    const id = Number(cb.dataset.id);
    if (!gamevideoPlaylists[currentGameVideoPlaylist].includes(id)) gamevideoPlaylists[currentGameVideoPlaylist].push(id);
  });
  touchPlaylistMeta(gamevideoPlaylistMeta, currentGameVideoPlaylist);
  renderPlaylistGameVideo();
  renderGameVideoPlaylists();
  saveGameVideoPlaylists();
  saveGameVideoPlaylistMeta();
});

document.getElementById("btn-add-all-gamevideo-to-playlist").addEventListener("click", () => {
  if (!currentGameVideoPlaylist || isSmartPlaylist(currentGameVideoPlaylist)) return alert("Select a playlist first");
  gamevideo.forEach(item => {
    if (!gamevideoPlaylists[currentGameVideoPlaylist].includes(item.id)) gamevideoPlaylists[currentGameVideoPlaylist].push(item.id);
  });
  touchPlaylistMeta(gamevideoPlaylistMeta, currentGameVideoPlaylist);
  renderPlaylistGameVideo();
  renderGameVideoPlaylists();
  saveGameVideoPlaylists();
  saveGameVideoPlaylistMeta();
});

document.getElementById("btn-remove-gamevideo-from-playlist").addEventListener("click", () => {
  if (!currentGameVideoPlaylist || isSmartPlaylist(currentGameVideoPlaylist)) return;
  const toRemove = Array.from(playlistGameVideo.querySelectorAll("input[type=checkbox]:checked")).map(cb => Number(cb.dataset.id));
  gamevideoPlaylists[currentGameVideoPlaylist] = gamevideoPlaylists[currentGameVideoPlaylist].filter(id => !toRemove.includes(id));
  touchPlaylistMeta(gamevideoPlaylistMeta, currentGameVideoPlaylist);
  renderPlaylistGameVideo();
  renderGameVideoPlaylists();
  saveGameVideoPlaylists();
  saveGameVideoPlaylistMeta();
});

document.getElementById("btn-clear-gamevideo-playlist").addEventListener("click", () => {
  if (!currentGameVideoPlaylist || isSmartPlaylist(currentGameVideoPlaylist)) return;
  gamevideoPlaylists[currentGameVideoPlaylist] = [];
  touchPlaylistMeta(gamevideoPlaylistMeta, currentGameVideoPlaylist);
  renderPlaylistGameVideo();
  renderGameVideoPlaylists();
  saveGameVideoPlaylists();
  saveGameVideoPlaylistMeta();
});

document.getElementById("btn-play-gamevideo-playlist").addEventListener("click", () => {
  const ids = getActivePlaylistIds(gamevideoPlaylistCtx());
  if (!currentGameVideoPlaylist || !ids.length) return alert("Select a playlist with game videos");
  gamevideoPlaylistPlaying = true;
  playGameVideoById(ids[0]);
});

document.getElementById("btn-export-gamevideo-playlist").addEventListener("click", () => {
  exportPlaylistFile(currentGameVideoPlaylist, currentGameVideoPlaylist ? getActivePlaylistIds(gamevideoPlaylistCtx()) : null, gamevideo);
});

document.getElementById("gamevideo-playlist-import").addEventListener("change", async e => {
  const file = e.target.files[0];
  if (!file) return;
  try {
    await importPlaylistFile(file, gamevideoDB, "gamevideo", gamevideo, gamevideoPlaylists, saveGameVideoPlaylists, renderPlaylistGameVideo, renderGameVideoPlaylists, selectGameVideoPlaylist, gamevideoPlaylistMeta, saveGameVideoPlaylistMeta, "video");
  } finally {
    e.target.value = "";
  }
  renderGameVideo(gamevideoSearch.value);
});

PLAYLIST_FOLDER_IMPORT_HANDLERS["gamevideo-playlist-import"] = async (files, folderName) => {
  await importPlaylistFolder(files, folderName, gamevideoDB, "gamevideo", gamevideo, gamevideoPlaylists, saveGameVideoPlaylists, renderPlaylistGameVideo, renderGameVideoPlaylists, selectGameVideoPlaylist, gamevideoPlaylistMeta, saveGameVideoPlaylistMeta, "video");
  renderGameVideo(gamevideoSearch.value);
};

(function enablePlaylistPanelDrop(wrapId, isValidId, getCurrentName, addToPlaylist, saveFn, renderListFn, renderNamesFn) {
  const wrap = document.getElementById(wrapId);
  if (!wrap) return;
  wrap.addEventListener("dragover", e => {
    if (!getCurrentName() || !e.dataTransfer.types.includes("text/plain")) return;
    e.preventDefault();
    e.dataTransfer.dropEffect = "copy";
    wrap.classList.add("drag-over");
  });
  wrap.addEventListener("dragleave", e => {
    if (!wrap.contains(e.relatedTarget)) wrap.classList.remove("drag-over");
  });
  wrap.addEventListener("drop", e => {
    e.preventDefault();
    wrap.classList.remove("drag-over");
    const name = getCurrentName();
    if (!name) return;
    const id = Number(e.dataTransfer.getData("text/plain"));
    if (!id || !isValidId(id)) return;
    addToPlaylist(name, id);
    saveFn();
    renderListFn();
    renderNamesFn();
  });
})("playlist-gamevideo-wrap", id => !!gamevideo.find(d => d.id === id), () => currentGameVideoPlaylist, (name, id) => {
  if (!gamevideoPlaylists[name].includes(id)) gamevideoPlaylists[name].push(id);
}, saveGameVideoPlaylists, renderPlaylistGameVideo, renderGameVideoPlaylists);

let gamemovie = [];

let currentGameMovieId = null;

let gamemoviePositions = {};

let gamemoviePlaylists = {};

let gamemoviePlaylistMeta = {};

let currentGameMoviePlaylist = null;

let gamemoviePlaylistPlaying = false;

let gamemovieLoopPlaylist = false;

let gamemoviePlaylistSortMode = "name";

let gamemovieRepeat = false;

let lastGameMoviePositionSave = 0;

let gamemovieDB;

const gamemovieSearch = document.getElementById("gamemovie-search");

const gamemovieUpload = document.getElementById("gamemovie-upload");

const gamemovieList = document.getElementById("gamemovie-list");

const gamemovieCount = document.getElementById("gamemovie-count");

const currentGameMovieDisplay = document.getElementById("current-gamemovie");

const gamemoviePlayer = document.getElementById("gamemovie-player");

const gamemovieProgress = document.getElementById("gamemovie-progress");

const gamemovieCurrentTimeEl = document.getElementById("gamemovie-current-time");

const gamemovieDurationEl = document.getElementById("gamemovie-duration");

const playPauseGameMovieBtn = document.getElementById("play-pause-gamemovie");

const nextGameMovieBtn = document.getElementById("next-gamemovie");

const prevGameMovieBtn = document.getElementById("prev-gamemovie");

const toggleRepeatGameMovieBtn = document.getElementById("toggle-repeat-gamemovie");

const gamemovieVolume = document.getElementById("gamemovie-volume");

const gamemovieMuteBtn = document.getElementById("gamemovie-mute-btn");

const gamemovieVolumeLabel = document.getElementById("gamemovie-volume-label");

const gamemovieSpeedGroup = document.getElementById("gamemovie-speed-group");

const gamemoviePlaylistsEl = document.getElementById("gamemovie-playlists");

const gamemoviePlaylistToolbarEl = document.getElementById("gamemovie-playlist-toolbar");

const gamemoviePlaylistName = document.getElementById("gamemovie-playlist-name");

const playlistGameMovie = document.getElementById("playlist-gamemovie");

const gamemoviePlaylistTitle = document.getElementById("gamemovie-playlist-title");

const gamemoviePlaylistHeaderEl = document.getElementById("gamemovie-playlist-header");

const selectAllGameMovieCheckbox = document.getElementById("select-all-gamemovie");

const deleteSelectedGameMovieBtn = document.getElementById("btn-delete-selected-gamemovie");

function openGameMovieDB() {
  return openTerminalDB("GameMoviePlayerDB", [ {
    name: "gamemovie"
  } ]);
}

async function loadGameMovieFromDB() {
  if (!gamemovieDB || !currentUserId) {
    gamemovie.length = 0;
    renderGameMovie(gamemovieSearch.value);
    return;
  }
  const rows = await loadUserRecordsIndexed(gamemovieDB, "gamemovie", currentUserId);
  gamemovie.length = 0;
  gamemovie.push(...rows);
  restoreListSortMode("gamemovie", gamemovie);
  renderGameMovie(gamemovieSearch.value);
}

function renderGameMovie(filter = "") {
  const f = filter.toLowerCase();
  const visible = gamemovie.filter(item => !f || item.name.toLowerCase().includes(f));
  renderListBatched(gamemovieList, visible, item => {
    const li = document.createElement("li");
    if (item.id === currentGameMovieId) li.classList.add("selected");
    const cb = document.createElement("input");
    cb.type = "checkbox";
    cb.dataset.id = item.id;
    cb.addEventListener("change", () => {
      li.classList.toggle("selected", cb.checked);
      const allChecked = Array.from(document.querySelectorAll("#gamemovie-list input[type=checkbox]")).every(c => c.checked);
      if (selectAllGameMovieCheckbox) selectAllGameMovieCheckbox.checked = allChecked;
    });
    const name = document.createElement("span");
    name.textContent = item.name;
    const playBtn = document.createElement("button");
    playBtn.textContent = "▶";
    playBtn.className = "media-row-play-btn";
    playBtn.addEventListener("click", () => playGameMovieById(item.id));
    const deleteBtn = document.createElement("button");
    deleteBtn.textContent = "✕";
    deleteBtn.addEventListener("click", () => deleteGameMovieById(item.id));
    li.append(cb, name, playBtn, deleteBtn);
    attachRowClickToggle(li, cb, playBtn);
    return li;
  });
  gamemovieCount.textContent = `Total Game Movies: ${gamemovie.length}`;
}

function playGameMovieById(id, isResume) {
  const item = gamemovie.find(v => v.id === id);
  if (!item) return;
  let url;
  try {
    url = URL.createObjectURL(item.blob);
  } catch (err) {
    console.error("Failed to create a playback URL", err);
    alert("Could not load this file for playback.");
    return;
  }
  currentGameMovieId = id;
  if (gamemoviePlayer.dataset.url) URL.revokeObjectURL(gamemoviePlayer.dataset.url);
  gamemoviePlayer.src = url;
  gamemoviePlayer.dataset.url = url;
  const resumeAt = gamemoviePositions[id];
  if (resumeAt) {
    const restorePosition = () => {
      if (resumeAt < gamemoviePlayer.duration - 2) gamemoviePlayer.currentTime = resumeAt;
      gamemoviePlayer.removeEventListener("loadedmetadata", restorePosition);
    };
    gamemoviePlayer.addEventListener("loadedmetadata", restorePosition);
  }
  currentGameMovieDisplay.textContent = item.name;
  gamemoviePlayer.play().then(() => {
    playPauseGameMovieBtn.textContent = "Pause";
  }).catch(err => {
    console.error("Playback failed to start", err);
    playPauseGameMovieBtn.textContent = "Play";
  });
  renderGameMovie(gamemovieSearch.value);
}

function stopGameMovie() {
  currentGameMovieId = null;
  gamemoviePlayer.pause();
  gamemoviePlayer.removeAttribute("src");
  if (gamemoviePlayer.dataset.url) {
    URL.revokeObjectURL(gamemoviePlayer.dataset.url);
    delete gamemoviePlayer.dataset.url;
  }
  currentGameMovieDisplay.textContent = "No game movie selected";
  playPauseGameMovieBtn.textContent = "Play";
  renderGameMovie(gamemovieSearch.value);
}

function playNextGameMovie() {
  const queuedId = consumeQueueNext("gamemovie");
  if (queuedId !== null) return playGameMovieById(queuedId);
  if (gamemoviePlaylistPlaying && currentGameMoviePlaylist) {
    const list = getActivePlaylistIds(gamemoviePlaylistCtx());
    const shuffle = !isSmartPlaylist(currentGameMoviePlaylist) && getPlaylistMeta(gamemoviePlaylistMeta, currentGameMoviePlaylist).shuffle;
    const next = pickNextInList(list, currentGameMovieId, shuffle);
    if (next !== null) return playGameMovieById(next);
    if (gamemovieLoopPlaylist && list.length) return playGameMovieById(shuffle ? list[Math.floor(Math.random() * list.length)] : list[0]);
    gamemoviePlaylistPlaying = false;
    return;
  }
  if (!gamemovie.length) return;
  const idx = gamemovie.findIndex(v => v.id === currentGameMovieId);
  const nextIdx = idx === -1 ? 0 : (idx + 1) % gamemovie.length;
  playGameMovieById(gamemovie[nextIdx].id);
}

function playPrevGameMovie() {
  if (gamemoviePlaylistPlaying && currentGameMoviePlaylist) {
    const list = getActivePlaylistIds(gamemoviePlaylistCtx());
    const idx = list.indexOf(currentGameMovieId);
    if (idx > 0) return playGameMovieById(list[idx - 1]);
    return;
  }
  if (!gamemovie.length) return;
  const idx = gamemovie.findIndex(v => v.id === currentGameMovieId);
  const prevIdx = idx <= 0 ? gamemovie.length - 1 : idx - 1;
  playGameMovieById(gamemovie[prevIdx].id);
}

function deleteGameMovieById(id) {
  if (!gamemovieDB) return;
  if (!confirm("Delete this item?")) return;
  const tx = gamemovieDB.transaction("gamemovie", "readwrite");
  tx.objectStore("gamemovie").delete(id);
  tx.oncomplete = () => {
    if (currentGameMovieId === id) stopGameMovie();
    delete gamemoviePositions[id];
    appSet("gamemoviePositions", gamemoviePositions);
    loadGameMovieFromDB();
  };
}

if (selectAllGameMovieCheckbox) {
  selectAllGameMovieCheckbox.addEventListener("change", () => {
    const checked = selectAllGameMovieCheckbox.checked;
    gamemovieList.querySelectorAll("li").forEach(li => {
      const cb = li.querySelector("input[type=checkbox]");
      if (!cb) return;
      cb.checked = checked;
      li.classList.toggle("selected", checked);
    });
  });
}

if (deleteSelectedGameMovieBtn) {
  deleteSelectedGameMovieBtn.addEventListener("click", () => {
    if (!gamemovieDB) return alert("Database not ready");
    const selected = document.querySelectorAll("#gamemovie-list input[type=checkbox]:checked");
    if (selected.length === 0) return alert("No items selected");
    if (!confirm("Delete selected items?")) return;
    const idsToRemove = Array.from(selected).map(cb => Number(cb.dataset.id)).filter(id => !isNaN(id));
    const tx = gamemovieDB.transaction("gamemovie", "readwrite");
    const store = tx.objectStore("gamemovie");
    idsToRemove.forEach(id => store.delete(id));
    tx.oncomplete = () => {
      if (idsToRemove.includes(currentGameMovieId)) stopGameMovie();
      idsToRemove.forEach(id => delete gamemoviePositions[id]);
      appSet("gamemoviePositions", gamemoviePositions);
      mediaQueues.gamemovie = mediaQueues.gamemovie.filter(id => !idsToRemove.includes(id));
      saveQueue("gamemovie");
      renderQueue("gamemovie");
      selectAllGameMovieCheckbox.checked = false;
      loadGameMovieFromDB();
    };
  });
}

gamemovieUpload.addEventListener("change", async e => {
  if (!gamemovieDB || !currentUserId) return;
  const rawFiles = [ ...e.target.files ];
  if (!rawFiles.length) return;
  const files = filterUploadedMediaFiles(rawFiles, "video");
  if (!files.length) {
    gamemovieUpload.value = "";
    return;
  }
  const existingKeys = new Set(gamemovie.map(v => `${v.name.toLowerCase()}|${v.blob.size}`));
  const newFiles = files.filter(f => !existingKeys.has(`${f.name.toLowerCase()}|${f.size}`));
  const skippedCount = files.length - newFiles.length;
  if (!newFiles.length) {
    gamemovieUpload.value = "";
    if (skippedCount) alert(`Skipped ${skippedCount} duplicate file(s) already in your library.`);
    return;
  }
  const tx = gamemovieDB.transaction("gamemovie", "readwrite");
  const store = tx.objectStore("gamemovie");
  newFiles.forEach(file => {
    store.add({
      name: file.name,
      blob: file,
      userId: currentUserId
    });
  });
  tx.oncomplete = () => {
    gamemovieUpload.value = "";
    loadGameMovieFromDB();
    if (skippedCount) alert(`Added ${newFiles.length} file(s). Skipped ${skippedCount} duplicate(s).`);
  };
  tx.onerror = () => {
    console.error("Failed to save uploaded file(s)", tx.error);
    alert("Could not save the uploaded file(s).");
  };
});

gamemovieSearch.addEventListener("input", debounce(() => renderGameMovie(gamemovieSearch.value)));

document.getElementById("btn-shuffle-gamemovie").addEventListener("click", () => {
  shuffleArray(gamemovie);
  saveListSortMode("gamemovie", "shuffle", gamemovie);
  renderGameMovie(gamemovieSearch.value);
});

document.getElementById("btn-sort-az-gamemovie").addEventListener("click", () => {
  gamemovie.sort((a, b) => a.name.localeCompare(b.name));
  saveListSortMode("gamemovie", "az", gamemovie);
  renderGameMovie(gamemovieSearch.value);
});

document.getElementById("btn-sort-za-gamemovie").addEventListener("click", () => {
  gamemovie.sort((a, b) => b.name.localeCompare(a.name));
  saveListSortMode("gamemovie", "za", gamemovie);
  renderGameMovie(gamemovieSearch.value);
});

playPauseGameMovieBtn.addEventListener("click", () => {
  if (!currentGameMovieId && gamemovie.length) return playGameMovieById(gamemovie[0].id);
  if (gamemoviePlayer.paused) {
    gamemoviePlayer.play();
    playPauseGameMovieBtn.textContent = "Pause";
  } else {
    gamemoviePlayer.pause();
    playPauseGameMovieBtn.textContent = "Play";
  }
});

nextGameMovieBtn.addEventListener("click", () => playNextGameMovie());

prevGameMovieBtn.addEventListener("click", () => playPrevGameMovie());

toggleRepeatGameMovieBtn.addEventListener("click", () => {
  gamemovieRepeat = !gamemovieRepeat;
  gamemoviePlayer.loop = gamemovieRepeat;
  toggleRepeatGameMovieBtn.textContent = `Repeat: ${gamemovieRepeat ? "On" : "Off"}`;
});

gamemoviePlayer.addEventListener("timeupdate", () => {
  if (!gamemoviePlayer.duration) return;
  gamemovieProgress.value = gamemoviePlayer.currentTime / gamemoviePlayer.duration * 100;
  updateRangeFill(gamemovieProgress);
  gamemovieCurrentTimeEl.textContent = formatTime(gamemoviePlayer.currentTime);
  gamemovieDurationEl.textContent = formatTime(gamemoviePlayer.duration);
  if (currentGameMovieId !== null) {
    const now = Date.now();
    if (now - lastGameMoviePositionSave > POSITION_SAVE_INTERVAL) {
      lastGameMoviePositionSave = now;
      gamemoviePositions[currentGameMovieId] = gamemoviePlayer.currentTime;
      appSet("gamemoviePositions", gamemoviePositions);
    }
  }
});

gamemovieProgress.addEventListener("input", () => {
  if (gamemoviePlayer.duration) gamemoviePlayer.currentTime = gamemovieProgress.value / 100 * gamemoviePlayer.duration;
  updateRangeFill(gamemovieProgress);
});

gamemoviePlayer.addEventListener("pause", () => {
  if (currentGameMovieId !== null && gamemoviePlayer.duration) {
    gamemoviePositions[currentGameMovieId] = gamemoviePlayer.currentTime;
    appSet("gamemoviePositions", gamemoviePositions);
  }
});

gamemoviePlayer.addEventListener("ended", () => {
  if (currentGameMovieId !== null) {
    delete gamemoviePositions[currentGameMovieId];
    appSet("gamemoviePositions", gamemoviePositions);
  }
  playNextGameMovie();
});

document.getElementById("forward-10-gamemovie").addEventListener("click", () => {
  gamemoviePlayer.currentTime += 10;
});

document.getElementById("rewind-10-gamemovie").addEventListener("click", () => {
  gamemoviePlayer.currentTime = Math.max(0, gamemoviePlayer.currentTime - 10);
});

function gamemoviePlaylistCtx() {
  return {
    playlistsObj: gamemoviePlaylists,
    metaObj: gamemoviePlaylistMeta,
    mediaArray: () => gamemovie,
    historyType: "gamemovie",
    listEl: gamemoviePlaylistsEl,
    toolbarEl: gamemoviePlaylistToolbarEl,
    tracksEl: playlistGameMovie,
    headerEl: gamemoviePlaylistHeaderEl,
    titleEl: gamemoviePlaylistTitle,
    getCurrent: () => currentGameMoviePlaylist,
    setCurrent: v => {
      currentGameMoviePlaylist = v;
    },
    getSortMode: () => gamemoviePlaylistSortMode,
    setSortMode: v => {
      gamemoviePlaylistSortMode = v;
      appSet("gamemoviePlaylistSortMode", v);
    },
    saveFn: saveGameMoviePlaylists,
    saveMetaFn: saveGameMoviePlaylistMeta,
    renderNamesFn: renderGameMoviePlaylists,
    renderTracksFn: renderPlaylistGameMovie,
    selectFn: selectGameMoviePlaylist,
    playByIdFn: id => playGameMovieById(id),
    currentPlayingId: () => currentGameMovieId,
    setPlaying: v => {
      gamemoviePlaylistPlaying = v;
    }
  };
}

function renderGameMoviePlaylists() {
  renderPlaylistNamesGeneric(gamemoviePlaylistCtx());
}

function selectGameMoviePlaylist(name) {
  currentGameMoviePlaylist = name;
  gamemoviePlaylistTitle.textContent = isSmartPlaylist(name) ? smartPlaylistLabel(name) : name;
  renderPlaylistGameMovie();
  renderGameMoviePlaylists();
}

function renderPlaylistGameMovie() {
  renderPlaylistTracksGeneric(gamemoviePlaylistCtx());
}

function saveGameMoviePlaylists() {
  appSet("gamemoviePlaylists", gamemoviePlaylists);
}

function saveGameMoviePlaylistMeta() {
  appSet("gamemoviePlaylistMeta", gamemoviePlaylistMeta);
}

document.getElementById("btn-create-gamemovie-playlist").addEventListener("click", () => {
  const name = gamemoviePlaylistName.value.trim();
  if (!name || gamemoviePlaylists[name] || isSmartPlaylist(name)) return alert("Invalid or duplicate playlist name");
  gamemoviePlaylists[name] = [];
  getPlaylistMeta(gamemoviePlaylistMeta, name);
  gamemoviePlaylistName.value = "";
  renderGameMoviePlaylists();
  saveGameMoviePlaylists();
  saveGameMoviePlaylistMeta();
});

document.getElementById("btn-delete-gamemovie-playlist").addEventListener("click", () => {
  if (!currentGameMoviePlaylist || isSmartPlaylist(currentGameMoviePlaylist)) return alert("Select a playlist first");
  delete gamemoviePlaylists[currentGameMoviePlaylist];
  delete gamemoviePlaylistMeta[currentGameMoviePlaylist];
  currentGameMoviePlaylist = null;
  gamemoviePlaylistTitle.textContent = "Select a playlist";
  renderPlaylistGameMovie();
  renderGameMoviePlaylists();
  saveGameMoviePlaylists();
  saveGameMoviePlaylistMeta();
});

document.getElementById("btn-add-selected-gamemovie-to-playlist").addEventListener("click", () => {
  if (!currentGameMoviePlaylist || isSmartPlaylist(currentGameMoviePlaylist)) return alert("Select a playlist first");
  document.querySelectorAll("#gamemovie-list input[type=checkbox]:checked").forEach(cb => {
    const id = Number(cb.dataset.id);
    if (!gamemoviePlaylists[currentGameMoviePlaylist].includes(id)) gamemoviePlaylists[currentGameMoviePlaylist].push(id);
  });
  touchPlaylistMeta(gamemoviePlaylistMeta, currentGameMoviePlaylist);
  renderPlaylistGameMovie();
  renderGameMoviePlaylists();
  saveGameMoviePlaylists();
  saveGameMoviePlaylistMeta();
});

document.getElementById("btn-add-all-gamemovie-to-playlist").addEventListener("click", () => {
  if (!currentGameMoviePlaylist || isSmartPlaylist(currentGameMoviePlaylist)) return alert("Select a playlist first");
  gamemovie.forEach(item => {
    if (!gamemoviePlaylists[currentGameMoviePlaylist].includes(item.id)) gamemoviePlaylists[currentGameMoviePlaylist].push(item.id);
  });
  touchPlaylistMeta(gamemoviePlaylistMeta, currentGameMoviePlaylist);
  renderPlaylistGameMovie();
  renderGameMoviePlaylists();
  saveGameMoviePlaylists();
  saveGameMoviePlaylistMeta();
});

document.getElementById("btn-remove-gamemovie-from-playlist").addEventListener("click", () => {
  if (!currentGameMoviePlaylist || isSmartPlaylist(currentGameMoviePlaylist)) return;
  const toRemove = Array.from(playlistGameMovie.querySelectorAll("input[type=checkbox]:checked")).map(cb => Number(cb.dataset.id));
  gamemoviePlaylists[currentGameMoviePlaylist] = gamemoviePlaylists[currentGameMoviePlaylist].filter(id => !toRemove.includes(id));
  touchPlaylistMeta(gamemoviePlaylistMeta, currentGameMoviePlaylist);
  renderPlaylistGameMovie();
  renderGameMoviePlaylists();
  saveGameMoviePlaylists();
  saveGameMoviePlaylistMeta();
});

document.getElementById("btn-clear-gamemovie-playlist").addEventListener("click", () => {
  if (!currentGameMoviePlaylist || isSmartPlaylist(currentGameMoviePlaylist)) return;
  gamemoviePlaylists[currentGameMoviePlaylist] = [];
  touchPlaylistMeta(gamemoviePlaylistMeta, currentGameMoviePlaylist);
  renderPlaylistGameMovie();
  renderGameMoviePlaylists();
  saveGameMoviePlaylists();
  saveGameMoviePlaylistMeta();
});

document.getElementById("btn-play-gamemovie-playlist").addEventListener("click", () => {
  const ids = getActivePlaylistIds(gamemoviePlaylistCtx());
  if (!currentGameMoviePlaylist || !ids.length) return alert("Select a playlist with game movies");
  gamemoviePlaylistPlaying = true;
  playGameMovieById(ids[0]);
});

document.getElementById("btn-export-gamemovie-playlist").addEventListener("click", () => {
  exportPlaylistFile(currentGameMoviePlaylist, currentGameMoviePlaylist ? getActivePlaylistIds(gamemoviePlaylistCtx()) : null, gamemovie);
});

document.getElementById("gamemovie-playlist-import").addEventListener("change", async e => {
  const file = e.target.files[0];
  if (!file) return;
  try {
    await importPlaylistFile(file, gamemovieDB, "gamemovie", gamemovie, gamemoviePlaylists, saveGameMoviePlaylists, renderPlaylistGameMovie, renderGameMoviePlaylists, selectGameMoviePlaylist, gamemoviePlaylistMeta, saveGameMoviePlaylistMeta, "video");
  } finally {
    e.target.value = "";
  }
  renderGameMovie(gamemovieSearch.value);
});

PLAYLIST_FOLDER_IMPORT_HANDLERS["gamemovie-playlist-import"] = async (files, folderName) => {
  await importPlaylistFolder(files, folderName, gamemovieDB, "gamemovie", gamemovie, gamemoviePlaylists, saveGameMoviePlaylists, renderPlaylistGameMovie, renderGameMoviePlaylists, selectGameMoviePlaylist, gamemoviePlaylistMeta, saveGameMoviePlaylistMeta, "video");
  renderGameMovie(gamemovieSearch.value);
};

(function enablePlaylistPanelDrop(wrapId, isValidId, getCurrentName, addToPlaylist, saveFn, renderListFn, renderNamesFn) {
  const wrap = document.getElementById(wrapId);
  if (!wrap) return;
  wrap.addEventListener("dragover", e => {
    if (!getCurrentName() || !e.dataTransfer.types.includes("text/plain")) return;
    e.preventDefault();
    e.dataTransfer.dropEffect = "copy";
    wrap.classList.add("drag-over");
  });
  wrap.addEventListener("dragleave", e => {
    if (!wrap.contains(e.relatedTarget)) wrap.classList.remove("drag-over");
  });
  wrap.addEventListener("drop", e => {
    e.preventDefault();
    wrap.classList.remove("drag-over");
    const name = getCurrentName();
    if (!name) return;
    const id = Number(e.dataTransfer.getData("text/plain"));
    if (!id || !isValidId(id)) return;
    addToPlaylist(name, id);
    saveFn();
    renderListFn();
    renderNamesFn();
  });
})("playlist-gamemovie-wrap", id => !!gamemovie.find(d => d.id === id), () => currentGameMoviePlaylist, (name, id) => {
  if (!gamemoviePlaylists[name].includes(id)) gamemoviePlaylists[name].push(id);
}, saveGameMoviePlaylists, renderPlaylistGameMovie, renderGameMoviePlaylists);

let bookvideo = [];

let currentBookVideoId = null;

let bookvideoPositions = {};

let bookvideoPlaylists = {};

let bookvideoPlaylistMeta = {};

let currentBookVideoPlaylist = null;

let bookvideoPlaylistPlaying = false;

let bookvideoLoopPlaylist = false;

let bookvideoPlaylistSortMode = "name";

let bookvideoRepeat = false;

let lastBookVideoPositionSave = 0;

let bookvideoDB;

const bookvideoSearch = document.getElementById("bookvideo-search");

const bookvideoUpload = document.getElementById("bookvideo-upload");

const bookvideoList = document.getElementById("bookvideo-list");

const bookvideoCount = document.getElementById("bookvideo-count");

const currentBookVideoDisplay = document.getElementById("current-bookvideo");

const bookvideoPlayer = document.getElementById("bookvideo-player");

const bookvideoProgress = document.getElementById("bookvideo-progress");

const bookvideoCurrentTimeEl = document.getElementById("bookvideo-current-time");

const bookvideoDurationEl = document.getElementById("bookvideo-duration");

const playPauseBookVideoBtn = document.getElementById("play-pause-bookvideo");

const nextBookVideoBtn = document.getElementById("next-bookvideo");

const prevBookVideoBtn = document.getElementById("prev-bookvideo");

const toggleRepeatBookVideoBtn = document.getElementById("toggle-repeat-bookvideo");

const bookvideoVolume = document.getElementById("bookvideo-volume");

const bookvideoMuteBtn = document.getElementById("bookvideo-mute-btn");

const bookvideoVolumeLabel = document.getElementById("bookvideo-volume-label");

const bookvideoSpeedGroup = document.getElementById("bookvideo-speed-group");

const bookvideoPlaylistsEl = document.getElementById("bookvideo-playlists");

const bookvideoPlaylistToolbarEl = document.getElementById("bookvideo-playlist-toolbar");

const bookvideoPlaylistName = document.getElementById("bookvideo-playlist-name");

const playlistBookVideo = document.getElementById("playlist-bookvideo");

const bookvideoPlaylistTitle = document.getElementById("bookvideo-playlist-title");

const bookvideoPlaylistHeaderEl = document.getElementById("bookvideo-playlist-header");

const selectAllBookVideoCheckbox = document.getElementById("select-all-bookvideo");

const deleteSelectedBookVideoBtn = document.getElementById("btn-delete-selected-bookvideo");

function openBookVideoDB() {
  return openTerminalDB("BookVideoPlayerDB", [ {
    name: "bookvideo"
  } ]);
}

async function loadBookVideoFromDB() {
  if (!bookvideoDB || !currentUserId) {
    bookvideo.length = 0;
    renderBookVideo(bookvideoSearch.value);
    return;
  }
  const rows = await loadUserRecordsIndexed(bookvideoDB, "bookvideo", currentUserId);
  bookvideo.length = 0;
  bookvideo.push(...rows);
  restoreListSortMode("bookvideo", bookvideo);
  renderBookVideo(bookvideoSearch.value);
}

function renderBookVideo(filter = "") {
  const f = filter.toLowerCase();
  const visible = bookvideo.filter(item => !f || item.name.toLowerCase().includes(f));
  renderListBatched(bookvideoList, visible, item => {
    const li = document.createElement("li");
    if (item.id === currentBookVideoId) li.classList.add("selected");
    const cb = document.createElement("input");
    cb.type = "checkbox";
    cb.dataset.id = item.id;
    cb.addEventListener("change", () => {
      li.classList.toggle("selected", cb.checked);
      const allChecked = Array.from(document.querySelectorAll("#bookvideo-list input[type=checkbox]")).every(c => c.checked);
      if (selectAllBookVideoCheckbox) selectAllBookVideoCheckbox.checked = allChecked;
    });
    const name = document.createElement("span");
    name.textContent = item.name;
    const playBtn = document.createElement("button");
    playBtn.textContent = "▶";
    playBtn.className = "media-row-play-btn";
    playBtn.addEventListener("click", () => playBookVideoById(item.id));
    const deleteBtn = document.createElement("button");
    deleteBtn.textContent = "✕";
    deleteBtn.addEventListener("click", () => deleteBookVideoById(item.id));
    li.append(cb, name, playBtn, deleteBtn);
    attachRowClickToggle(li, cb, playBtn);
    return li;
  });
  bookvideoCount.textContent = `Total Book Videos: ${bookvideo.length}`;
}

function playBookVideoById(id, isResume) {
  const item = bookvideo.find(v => v.id === id);
  if (!item) return;
  let url;
  try {
    url = URL.createObjectURL(item.blob);
  } catch (err) {
    console.error("Failed to create a playback URL", err);
    alert("Could not load this file for playback.");
    return;
  }
  currentBookVideoId = id;
  if (bookvideoPlayer.dataset.url) URL.revokeObjectURL(bookvideoPlayer.dataset.url);
  bookvideoPlayer.src = url;
  bookvideoPlayer.dataset.url = url;
  const resumeAt = bookvideoPositions[id];
  if (resumeAt) {
    const restorePosition = () => {
      if (resumeAt < bookvideoPlayer.duration - 2) bookvideoPlayer.currentTime = resumeAt;
      bookvideoPlayer.removeEventListener("loadedmetadata", restorePosition);
    };
    bookvideoPlayer.addEventListener("loadedmetadata", restorePosition);
  }
  currentBookVideoDisplay.textContent = item.name;
  bookvideoPlayer.play().then(() => {
    playPauseBookVideoBtn.textContent = "Pause";
  }).catch(err => {
    console.error("Playback failed to start", err);
    playPauseBookVideoBtn.textContent = "Play";
  });
  renderBookVideo(bookvideoSearch.value);
}

function stopBookVideo() {
  currentBookVideoId = null;
  bookvideoPlayer.pause();
  bookvideoPlayer.removeAttribute("src");
  if (bookvideoPlayer.dataset.url) {
    URL.revokeObjectURL(bookvideoPlayer.dataset.url);
    delete bookvideoPlayer.dataset.url;
  }
  currentBookVideoDisplay.textContent = "No book video selected";
  playPauseBookVideoBtn.textContent = "Play";
  renderBookVideo(bookvideoSearch.value);
}

function playNextBookVideo() {
  const queuedId = consumeQueueNext("bookvideo");
  if (queuedId !== null) return playBookVideoById(queuedId);
  if (bookvideoPlaylistPlaying && currentBookVideoPlaylist) {
    const list = getActivePlaylistIds(bookvideoPlaylistCtx());
    const shuffle = !isSmartPlaylist(currentBookVideoPlaylist) && getPlaylistMeta(bookvideoPlaylistMeta, currentBookVideoPlaylist).shuffle;
    const next = pickNextInList(list, currentBookVideoId, shuffle);
    if (next !== null) return playBookVideoById(next);
    if (bookvideoLoopPlaylist && list.length) return playBookVideoById(shuffle ? list[Math.floor(Math.random() * list.length)] : list[0]);
    bookvideoPlaylistPlaying = false;
    return;
  }
  if (!bookvideo.length) return;
  const idx = bookvideo.findIndex(v => v.id === currentBookVideoId);
  const nextIdx = idx === -1 ? 0 : (idx + 1) % bookvideo.length;
  playBookVideoById(bookvideo[nextIdx].id);
}

function playPrevBookVideo() {
  if (bookvideoPlaylistPlaying && currentBookVideoPlaylist) {
    const list = getActivePlaylistIds(bookvideoPlaylistCtx());
    const idx = list.indexOf(currentBookVideoId);
    if (idx > 0) return playBookVideoById(list[idx - 1]);
    return;
  }
  if (!bookvideo.length) return;
  const idx = bookvideo.findIndex(v => v.id === currentBookVideoId);
  const prevIdx = idx <= 0 ? bookvideo.length - 1 : idx - 1;
  playBookVideoById(bookvideo[prevIdx].id);
}

function deleteBookVideoById(id) {
  if (!bookvideoDB) return;
  if (!confirm("Delete this item?")) return;
  const tx = bookvideoDB.transaction("bookvideo", "readwrite");
  tx.objectStore("bookvideo").delete(id);
  tx.oncomplete = () => {
    if (currentBookVideoId === id) stopBookVideo();
    delete bookvideoPositions[id];
    appSet("bookvideoPositions", bookvideoPositions);
    loadBookVideoFromDB();
  };
}

if (selectAllBookVideoCheckbox) {
  selectAllBookVideoCheckbox.addEventListener("change", () => {
    const checked = selectAllBookVideoCheckbox.checked;
    bookvideoList.querySelectorAll("li").forEach(li => {
      const cb = li.querySelector("input[type=checkbox]");
      if (!cb) return;
      cb.checked = checked;
      li.classList.toggle("selected", checked);
    });
  });
}

if (deleteSelectedBookVideoBtn) {
  deleteSelectedBookVideoBtn.addEventListener("click", () => {
    if (!bookvideoDB) return alert("Database not ready");
    const selected = document.querySelectorAll("#bookvideo-list input[type=checkbox]:checked");
    if (selected.length === 0) return alert("No items selected");
    if (!confirm("Delete selected items?")) return;
    const idsToRemove = Array.from(selected).map(cb => Number(cb.dataset.id)).filter(id => !isNaN(id));
    const tx = bookvideoDB.transaction("bookvideo", "readwrite");
    const store = tx.objectStore("bookvideo");
    idsToRemove.forEach(id => store.delete(id));
    tx.oncomplete = () => {
      if (idsToRemove.includes(currentBookVideoId)) stopBookVideo();
      idsToRemove.forEach(id => delete bookvideoPositions[id]);
      appSet("bookvideoPositions", bookvideoPositions);
      mediaQueues.bookvideo = mediaQueues.bookvideo.filter(id => !idsToRemove.includes(id));
      saveQueue("bookvideo");
      renderQueue("bookvideo");
      selectAllBookVideoCheckbox.checked = false;
      loadBookVideoFromDB();
    };
  });
}

bookvideoUpload.addEventListener("change", async e => {
  if (!bookvideoDB || !currentUserId) return;
  const rawFiles = [ ...e.target.files ];
  if (!rawFiles.length) return;
  const files = filterUploadedMediaFiles(rawFiles, "video");
  if (!files.length) {
    bookvideoUpload.value = "";
    return;
  }
  const existingKeys = new Set(bookvideo.map(v => `${v.name.toLowerCase()}|${v.blob.size}`));
  const newFiles = files.filter(f => !existingKeys.has(`${f.name.toLowerCase()}|${f.size}`));
  const skippedCount = files.length - newFiles.length;
  if (!newFiles.length) {
    bookvideoUpload.value = "";
    if (skippedCount) alert(`Skipped ${skippedCount} duplicate file(s) already in your library.`);
    return;
  }
  const tx = bookvideoDB.transaction("bookvideo", "readwrite");
  const store = tx.objectStore("bookvideo");
  newFiles.forEach(file => {
    store.add({
      name: file.name,
      blob: file,
      userId: currentUserId
    });
  });
  tx.oncomplete = () => {
    bookvideoUpload.value = "";
    loadBookVideoFromDB();
    if (skippedCount) alert(`Added ${newFiles.length} file(s). Skipped ${skippedCount} duplicate(s).`);
  };
  tx.onerror = () => {
    console.error("Failed to save uploaded file(s)", tx.error);
    alert("Could not save the uploaded file(s).");
  };
});

bookvideoSearch.addEventListener("input", debounce(() => renderBookVideo(bookvideoSearch.value)));

document.getElementById("btn-shuffle-bookvideo").addEventListener("click", () => {
  shuffleArray(bookvideo);
  saveListSortMode("bookvideo", "shuffle", bookvideo);
  renderBookVideo(bookvideoSearch.value);
});

document.getElementById("btn-sort-az-bookvideo").addEventListener("click", () => {
  bookvideo.sort((a, b) => a.name.localeCompare(b.name));
  saveListSortMode("bookvideo", "az", bookvideo);
  renderBookVideo(bookvideoSearch.value);
});

document.getElementById("btn-sort-za-bookvideo").addEventListener("click", () => {
  bookvideo.sort((a, b) => b.name.localeCompare(a.name));
  saveListSortMode("bookvideo", "za", bookvideo);
  renderBookVideo(bookvideoSearch.value);
});

playPauseBookVideoBtn.addEventListener("click", () => {
  if (!currentBookVideoId && bookvideo.length) return playBookVideoById(bookvideo[0].id);
  if (bookvideoPlayer.paused) {
    bookvideoPlayer.play();
    playPauseBookVideoBtn.textContent = "Pause";
  } else {
    bookvideoPlayer.pause();
    playPauseBookVideoBtn.textContent = "Play";
  }
});

nextBookVideoBtn.addEventListener("click", () => playNextBookVideo());

prevBookVideoBtn.addEventListener("click", () => playPrevBookVideo());

toggleRepeatBookVideoBtn.addEventListener("click", () => {
  bookvideoRepeat = !bookvideoRepeat;
  bookvideoPlayer.loop = bookvideoRepeat;
  toggleRepeatBookVideoBtn.textContent = `Repeat: ${bookvideoRepeat ? "On" : "Off"}`;
});

bookvideoPlayer.addEventListener("timeupdate", () => {
  if (!bookvideoPlayer.duration) return;
  bookvideoProgress.value = bookvideoPlayer.currentTime / bookvideoPlayer.duration * 100;
  updateRangeFill(bookvideoProgress);
  bookvideoCurrentTimeEl.textContent = formatTime(bookvideoPlayer.currentTime);
  bookvideoDurationEl.textContent = formatTime(bookvideoPlayer.duration);
  if (currentBookVideoId !== null) {
    const now = Date.now();
    if (now - lastBookVideoPositionSave > POSITION_SAVE_INTERVAL) {
      lastBookVideoPositionSave = now;
      bookvideoPositions[currentBookVideoId] = bookvideoPlayer.currentTime;
      appSet("bookvideoPositions", bookvideoPositions);
    }
  }
});

bookvideoProgress.addEventListener("input", () => {
  if (bookvideoPlayer.duration) bookvideoPlayer.currentTime = bookvideoProgress.value / 100 * bookvideoPlayer.duration;
  updateRangeFill(bookvideoProgress);
});

bookvideoPlayer.addEventListener("pause", () => {
  if (currentBookVideoId !== null && bookvideoPlayer.duration) {
    bookvideoPositions[currentBookVideoId] = bookvideoPlayer.currentTime;
    appSet("bookvideoPositions", bookvideoPositions);
  }
});

bookvideoPlayer.addEventListener("ended", () => {
  if (currentBookVideoId !== null) {
    delete bookvideoPositions[currentBookVideoId];
    appSet("bookvideoPositions", bookvideoPositions);
  }
  playNextBookVideo();
});

document.getElementById("forward-10-bookvideo").addEventListener("click", () => {
  bookvideoPlayer.currentTime += 10;
});

document.getElementById("rewind-10-bookvideo").addEventListener("click", () => {
  bookvideoPlayer.currentTime = Math.max(0, bookvideoPlayer.currentTime - 10);
});

function bookvideoPlaylistCtx() {
  return {
    playlistsObj: bookvideoPlaylists,
    metaObj: bookvideoPlaylistMeta,
    mediaArray: () => bookvideo,
    historyType: "bookvideo",
    listEl: bookvideoPlaylistsEl,
    toolbarEl: bookvideoPlaylistToolbarEl,
    tracksEl: playlistBookVideo,
    headerEl: bookvideoPlaylistHeaderEl,
    titleEl: bookvideoPlaylistTitle,
    getCurrent: () => currentBookVideoPlaylist,
    setCurrent: v => {
      currentBookVideoPlaylist = v;
    },
    getSortMode: () => bookvideoPlaylistSortMode,
    setSortMode: v => {
      bookvideoPlaylistSortMode = v;
      appSet("bookvideoPlaylistSortMode", v);
    },
    saveFn: saveBookVideoPlaylists,
    saveMetaFn: saveBookVideoPlaylistMeta,
    renderNamesFn: renderBookVideoPlaylists,
    renderTracksFn: renderPlaylistBookVideo,
    selectFn: selectBookVideoPlaylist,
    playByIdFn: id => playBookVideoById(id),
    currentPlayingId: () => currentBookVideoId,
    setPlaying: v => {
      bookvideoPlaylistPlaying = v;
    }
  };
}

function renderBookVideoPlaylists() {
  renderPlaylistNamesGeneric(bookvideoPlaylistCtx());
}

function selectBookVideoPlaylist(name) {
  currentBookVideoPlaylist = name;
  bookvideoPlaylistTitle.textContent = isSmartPlaylist(name) ? smartPlaylistLabel(name) : name;
  renderPlaylistBookVideo();
  renderBookVideoPlaylists();
}

function renderPlaylistBookVideo() {
  renderPlaylistTracksGeneric(bookvideoPlaylistCtx());
}

function saveBookVideoPlaylists() {
  appSet("bookvideoPlaylists", bookvideoPlaylists);
}

function saveBookVideoPlaylistMeta() {
  appSet("bookvideoPlaylistMeta", bookvideoPlaylistMeta);
}

document.getElementById("btn-create-bookvideo-playlist").addEventListener("click", () => {
  const name = bookvideoPlaylistName.value.trim();
  if (!name || bookvideoPlaylists[name] || isSmartPlaylist(name)) return alert("Invalid or duplicate playlist name");
  bookvideoPlaylists[name] = [];
  getPlaylistMeta(bookvideoPlaylistMeta, name);
  bookvideoPlaylistName.value = "";
  renderBookVideoPlaylists();
  saveBookVideoPlaylists();
  saveBookVideoPlaylistMeta();
});

document.getElementById("btn-delete-bookvideo-playlist").addEventListener("click", () => {
  if (!currentBookVideoPlaylist || isSmartPlaylist(currentBookVideoPlaylist)) return alert("Select a playlist first");
  delete bookvideoPlaylists[currentBookVideoPlaylist];
  delete bookvideoPlaylistMeta[currentBookVideoPlaylist];
  currentBookVideoPlaylist = null;
  bookvideoPlaylistTitle.textContent = "Select a playlist";
  renderPlaylistBookVideo();
  renderBookVideoPlaylists();
  saveBookVideoPlaylists();
  saveBookVideoPlaylistMeta();
});

document.getElementById("btn-add-selected-bookvideo-to-playlist").addEventListener("click", () => {
  if (!currentBookVideoPlaylist || isSmartPlaylist(currentBookVideoPlaylist)) return alert("Select a playlist first");
  document.querySelectorAll("#bookvideo-list input[type=checkbox]:checked").forEach(cb => {
    const id = Number(cb.dataset.id);
    if (!bookvideoPlaylists[currentBookVideoPlaylist].includes(id)) bookvideoPlaylists[currentBookVideoPlaylist].push(id);
  });
  touchPlaylistMeta(bookvideoPlaylistMeta, currentBookVideoPlaylist);
  renderPlaylistBookVideo();
  renderBookVideoPlaylists();
  saveBookVideoPlaylists();
  saveBookVideoPlaylistMeta();
});

document.getElementById("btn-add-all-bookvideo-to-playlist").addEventListener("click", () => {
  if (!currentBookVideoPlaylist || isSmartPlaylist(currentBookVideoPlaylist)) return alert("Select a playlist first");
  bookvideo.forEach(item => {
    if (!bookvideoPlaylists[currentBookVideoPlaylist].includes(item.id)) bookvideoPlaylists[currentBookVideoPlaylist].push(item.id);
  });
  touchPlaylistMeta(bookvideoPlaylistMeta, currentBookVideoPlaylist);
  renderPlaylistBookVideo();
  renderBookVideoPlaylists();
  saveBookVideoPlaylists();
  saveBookVideoPlaylistMeta();
});

document.getElementById("btn-remove-bookvideo-from-playlist").addEventListener("click", () => {
  if (!currentBookVideoPlaylist || isSmartPlaylist(currentBookVideoPlaylist)) return;
  const toRemove = Array.from(playlistBookVideo.querySelectorAll("input[type=checkbox]:checked")).map(cb => Number(cb.dataset.id));
  bookvideoPlaylists[currentBookVideoPlaylist] = bookvideoPlaylists[currentBookVideoPlaylist].filter(id => !toRemove.includes(id));
  touchPlaylistMeta(bookvideoPlaylistMeta, currentBookVideoPlaylist);
  renderPlaylistBookVideo();
  renderBookVideoPlaylists();
  saveBookVideoPlaylists();
  saveBookVideoPlaylistMeta();
});

document.getElementById("btn-clear-bookvideo-playlist").addEventListener("click", () => {
  if (!currentBookVideoPlaylist || isSmartPlaylist(currentBookVideoPlaylist)) return;
  bookvideoPlaylists[currentBookVideoPlaylist] = [];
  touchPlaylistMeta(bookvideoPlaylistMeta, currentBookVideoPlaylist);
  renderPlaylistBookVideo();
  renderBookVideoPlaylists();
  saveBookVideoPlaylists();
  saveBookVideoPlaylistMeta();
});

document.getElementById("btn-play-bookvideo-playlist").addEventListener("click", () => {
  const ids = getActivePlaylistIds(bookvideoPlaylistCtx());
  if (!currentBookVideoPlaylist || !ids.length) return alert("Select a playlist with book videos");
  bookvideoPlaylistPlaying = true;
  playBookVideoById(ids[0]);
});

document.getElementById("btn-export-bookvideo-playlist").addEventListener("click", () => {
  exportPlaylistFile(currentBookVideoPlaylist, currentBookVideoPlaylist ? getActivePlaylistIds(bookvideoPlaylistCtx()) : null, bookvideo);
});

document.getElementById("bookvideo-playlist-import").addEventListener("change", async e => {
  const file = e.target.files[0];
  if (!file) return;
  try {
    await importPlaylistFile(file, bookvideoDB, "bookvideo", bookvideo, bookvideoPlaylists, saveBookVideoPlaylists, renderPlaylistBookVideo, renderBookVideoPlaylists, selectBookVideoPlaylist, bookvideoPlaylistMeta, saveBookVideoPlaylistMeta, "video");
  } finally {
    e.target.value = "";
  }
  renderBookVideo(bookvideoSearch.value);
});

PLAYLIST_FOLDER_IMPORT_HANDLERS["bookvideo-playlist-import"] = async (files, folderName) => {
  await importPlaylistFolder(files, folderName, bookvideoDB, "bookvideo", bookvideo, bookvideoPlaylists, saveBookVideoPlaylists, renderPlaylistBookVideo, renderBookVideoPlaylists, selectBookVideoPlaylist, bookvideoPlaylistMeta, saveBookVideoPlaylistMeta, "video");
  renderBookVideo(bookvideoSearch.value);
};

(function enablePlaylistPanelDrop(wrapId, isValidId, getCurrentName, addToPlaylist, saveFn, renderListFn, renderNamesFn) {
  const wrap = document.getElementById(wrapId);
  if (!wrap) return;
  wrap.addEventListener("dragover", e => {
    if (!getCurrentName() || !e.dataTransfer.types.includes("text/plain")) return;
    e.preventDefault();
    e.dataTransfer.dropEffect = "copy";
    wrap.classList.add("drag-over");
  });
  wrap.addEventListener("dragleave", e => {
    if (!wrap.contains(e.relatedTarget)) wrap.classList.remove("drag-over");
  });
  wrap.addEventListener("drop", e => {
    e.preventDefault();
    wrap.classList.remove("drag-over");
    const name = getCurrentName();
    if (!name) return;
    const id = Number(e.dataTransfer.getData("text/plain"));
    if (!id || !isValidId(id)) return;
    addToPlaylist(name, id);
    saveFn();
    renderListFn();
    renderNamesFn();
  });
})("playlist-bookvideo-wrap", id => !!bookvideo.find(d => d.id === id), () => currentBookVideoPlaylist, (name, id) => {
  if (!bookvideoPlaylists[name].includes(id)) bookvideoPlaylists[name].push(id);
}, saveBookVideoPlaylists, renderPlaylistBookVideo, renderBookVideoPlaylists);

let bookmovie = [];

let currentBookMovieId = null;

let bookmoviePositions = {};

let bookmoviePlaylists = {};

let bookmoviePlaylistMeta = {};

let currentBookMoviePlaylist = null;

let bookmoviePlaylistPlaying = false;

let bookmovieLoopPlaylist = false;

let bookmoviePlaylistSortMode = "name";

let bookmovieRepeat = false;

let lastBookMoviePositionSave = 0;

let bookmovieDB;

const bookmovieSearch = document.getElementById("bookmovie-search");

const bookmovieUpload = document.getElementById("bookmovie-upload");

const bookmovieList = document.getElementById("bookmovie-list");

const bookmovieCount = document.getElementById("bookmovie-count");

const currentBookMovieDisplay = document.getElementById("current-bookmovie");

const bookmoviePlayer = document.getElementById("bookmovie-player");

const bookmovieProgress = document.getElementById("bookmovie-progress");

const bookmovieCurrentTimeEl = document.getElementById("bookmovie-current-time");

const bookmovieDurationEl = document.getElementById("bookmovie-duration");

const playPauseBookMovieBtn = document.getElementById("play-pause-bookmovie");

const nextBookMovieBtn = document.getElementById("next-bookmovie");

const prevBookMovieBtn = document.getElementById("prev-bookmovie");

const toggleRepeatBookMovieBtn = document.getElementById("toggle-repeat-bookmovie");

const bookmovieVolume = document.getElementById("bookmovie-volume");

const bookmovieMuteBtn = document.getElementById("bookmovie-mute-btn");

const bookmovieVolumeLabel = document.getElementById("bookmovie-volume-label");

const bookmovieSpeedGroup = document.getElementById("bookmovie-speed-group");

const bookmoviePlaylistsEl = document.getElementById("bookmovie-playlists");

const bookmoviePlaylistToolbarEl = document.getElementById("bookmovie-playlist-toolbar");

const bookmoviePlaylistName = document.getElementById("bookmovie-playlist-name");

const playlistBookMovie = document.getElementById("playlist-bookmovie");

const bookmoviePlaylistTitle = document.getElementById("bookmovie-playlist-title");

const bookmoviePlaylistHeaderEl = document.getElementById("bookmovie-playlist-header");

const selectAllBookMovieCheckbox = document.getElementById("select-all-bookmovie");

const deleteSelectedBookMovieBtn = document.getElementById("btn-delete-selected-bookmovie");

function openBookMovieDB() {
  return openTerminalDB("BookMoviePlayerDB", [ {
    name: "bookmovie"
  } ]);
}

async function loadBookMovieFromDB() {
  if (!bookmovieDB || !currentUserId) {
    bookmovie.length = 0;
    renderBookMovie(bookmovieSearch.value);
    return;
  }
  const rows = await loadUserRecordsIndexed(bookmovieDB, "bookmovie", currentUserId);
  bookmovie.length = 0;
  bookmovie.push(...rows);
  restoreListSortMode("bookmovie", bookmovie);
  renderBookMovie(bookmovieSearch.value);
}

function renderBookMovie(filter = "") {
  const f = filter.toLowerCase();
  const visible = bookmovie.filter(item => !f || item.name.toLowerCase().includes(f));
  renderListBatched(bookmovieList, visible, item => {
    const li = document.createElement("li");
    if (item.id === currentBookMovieId) li.classList.add("selected");
    const cb = document.createElement("input");
    cb.type = "checkbox";
    cb.dataset.id = item.id;
    cb.addEventListener("change", () => {
      li.classList.toggle("selected", cb.checked);
      const allChecked = Array.from(document.querySelectorAll("#bookmovie-list input[type=checkbox]")).every(c => c.checked);
      if (selectAllBookMovieCheckbox) selectAllBookMovieCheckbox.checked = allChecked;
    });
    const name = document.createElement("span");
    name.textContent = item.name;
    const playBtn = document.createElement("button");
    playBtn.textContent = "▶";
    playBtn.className = "media-row-play-btn";
    playBtn.addEventListener("click", () => playBookMovieById(item.id));
    const deleteBtn = document.createElement("button");
    deleteBtn.textContent = "✕";
    deleteBtn.addEventListener("click", () => deleteBookMovieById(item.id));
    li.append(cb, name, playBtn, deleteBtn);
    attachRowClickToggle(li, cb, playBtn);
    return li;
  });
  bookmovieCount.textContent = `Total Book Movies: ${bookmovie.length}`;
}

function playBookMovieById(id, isResume) {
  const item = bookmovie.find(v => v.id === id);
  if (!item) return;
  let url;
  try {
    url = URL.createObjectURL(item.blob);
  } catch (err) {
    console.error("Failed to create a playback URL", err);
    alert("Could not load this file for playback.");
    return;
  }
  currentBookMovieId = id;
  if (bookmoviePlayer.dataset.url) URL.revokeObjectURL(bookmoviePlayer.dataset.url);
  bookmoviePlayer.src = url;
  bookmoviePlayer.dataset.url = url;
  const resumeAt = bookmoviePositions[id];
  if (resumeAt) {
    const restorePosition = () => {
      if (resumeAt < bookmoviePlayer.duration - 2) bookmoviePlayer.currentTime = resumeAt;
      bookmoviePlayer.removeEventListener("loadedmetadata", restorePosition);
    };
    bookmoviePlayer.addEventListener("loadedmetadata", restorePosition);
  }
  currentBookMovieDisplay.textContent = item.name;
  bookmoviePlayer.play().then(() => {
    playPauseBookMovieBtn.textContent = "Pause";
  }).catch(err => {
    console.error("Playback failed to start", err);
    playPauseBookMovieBtn.textContent = "Play";
  });
  renderBookMovie(bookmovieSearch.value);
}

function stopBookMovie() {
  currentBookMovieId = null;
  bookmoviePlayer.pause();
  bookmoviePlayer.removeAttribute("src");
  if (bookmoviePlayer.dataset.url) {
    URL.revokeObjectURL(bookmoviePlayer.dataset.url);
    delete bookmoviePlayer.dataset.url;
  }
  currentBookMovieDisplay.textContent = "No book movie selected";
  playPauseBookMovieBtn.textContent = "Play";
  renderBookMovie(bookmovieSearch.value);
}

function playNextBookMovie() {
  const queuedId = consumeQueueNext("bookmovie");
  if (queuedId !== null) return playBookMovieById(queuedId);
  if (bookmoviePlaylistPlaying && currentBookMoviePlaylist) {
    const list = getActivePlaylistIds(bookmoviePlaylistCtx());
    const shuffle = !isSmartPlaylist(currentBookMoviePlaylist) && getPlaylistMeta(bookmoviePlaylistMeta, currentBookMoviePlaylist).shuffle;
    const next = pickNextInList(list, currentBookMovieId, shuffle);
    if (next !== null) return playBookMovieById(next);
    if (bookmovieLoopPlaylist && list.length) return playBookMovieById(shuffle ? list[Math.floor(Math.random() * list.length)] : list[0]);
    bookmoviePlaylistPlaying = false;
    return;
  }
  if (!bookmovie.length) return;
  const idx = bookmovie.findIndex(v => v.id === currentBookMovieId);
  const nextIdx = idx === -1 ? 0 : (idx + 1) % bookmovie.length;
  playBookMovieById(bookmovie[nextIdx].id);
}

function playPrevBookMovie() {
  if (bookmoviePlaylistPlaying && currentBookMoviePlaylist) {
    const list = getActivePlaylistIds(bookmoviePlaylistCtx());
    const idx = list.indexOf(currentBookMovieId);
    if (idx > 0) return playBookMovieById(list[idx - 1]);
    return;
  }
  if (!bookmovie.length) return;
  const idx = bookmovie.findIndex(v => v.id === currentBookMovieId);
  const prevIdx = idx <= 0 ? bookmovie.length - 1 : idx - 1;
  playBookMovieById(bookmovie[prevIdx].id);
}

function deleteBookMovieById(id) {
  if (!bookmovieDB) return;
  if (!confirm("Delete this item?")) return;
  const tx = bookmovieDB.transaction("bookmovie", "readwrite");
  tx.objectStore("bookmovie").delete(id);
  tx.oncomplete = () => {
    if (currentBookMovieId === id) stopBookMovie();
    delete bookmoviePositions[id];
    appSet("bookmoviePositions", bookmoviePositions);
    loadBookMovieFromDB();
  };
}

if (selectAllBookMovieCheckbox) {
  selectAllBookMovieCheckbox.addEventListener("change", () => {
    const checked = selectAllBookMovieCheckbox.checked;
    bookmovieList.querySelectorAll("li").forEach(li => {
      const cb = li.querySelector("input[type=checkbox]");
      if (!cb) return;
      cb.checked = checked;
      li.classList.toggle("selected", checked);
    });
  });
}

if (deleteSelectedBookMovieBtn) {
  deleteSelectedBookMovieBtn.addEventListener("click", () => {
    if (!bookmovieDB) return alert("Database not ready");
    const selected = document.querySelectorAll("#bookmovie-list input[type=checkbox]:checked");
    if (selected.length === 0) return alert("No items selected");
    if (!confirm("Delete selected items?")) return;
    const idsToRemove = Array.from(selected).map(cb => Number(cb.dataset.id)).filter(id => !isNaN(id));
    const tx = bookmovieDB.transaction("bookmovie", "readwrite");
    const store = tx.objectStore("bookmovie");
    idsToRemove.forEach(id => store.delete(id));
    tx.oncomplete = () => {
      if (idsToRemove.includes(currentBookMovieId)) stopBookMovie();
      idsToRemove.forEach(id => delete bookmoviePositions[id]);
      appSet("bookmoviePositions", bookmoviePositions);
      mediaQueues.bookmovie = mediaQueues.bookmovie.filter(id => !idsToRemove.includes(id));
      saveQueue("bookmovie");
      renderQueue("bookmovie");
      selectAllBookMovieCheckbox.checked = false;
      loadBookMovieFromDB();
    };
  });
}

bookmovieUpload.addEventListener("change", async e => {
  if (!bookmovieDB || !currentUserId) return;
  const rawFiles = [ ...e.target.files ];
  if (!rawFiles.length) return;
  const files = filterUploadedMediaFiles(rawFiles, "video");
  if (!files.length) {
    bookmovieUpload.value = "";
    return;
  }
  const existingKeys = new Set(bookmovie.map(v => `${v.name.toLowerCase()}|${v.blob.size}`));
  const newFiles = files.filter(f => !existingKeys.has(`${f.name.toLowerCase()}|${f.size}`));
  const skippedCount = files.length - newFiles.length;
  if (!newFiles.length) {
    bookmovieUpload.value = "";
    if (skippedCount) alert(`Skipped ${skippedCount} duplicate file(s) already in your library.`);
    return;
  }
  const tx = bookmovieDB.transaction("bookmovie", "readwrite");
  const store = tx.objectStore("bookmovie");
  newFiles.forEach(file => {
    store.add({
      name: file.name,
      blob: file,
      userId: currentUserId
    });
  });
  tx.oncomplete = () => {
    bookmovieUpload.value = "";
    loadBookMovieFromDB();
    if (skippedCount) alert(`Added ${newFiles.length} file(s). Skipped ${skippedCount} duplicate(s).`);
  };
  tx.onerror = () => {
    console.error("Failed to save uploaded file(s)", tx.error);
    alert("Could not save the uploaded file(s).");
  };
});

bookmovieSearch.addEventListener("input", debounce(() => renderBookMovie(bookmovieSearch.value)));

document.getElementById("btn-shuffle-bookmovie").addEventListener("click", () => {
  shuffleArray(bookmovie);
  saveListSortMode("bookmovie", "shuffle", bookmovie);
  renderBookMovie(bookmovieSearch.value);
});

document.getElementById("btn-sort-az-bookmovie").addEventListener("click", () => {
  bookmovie.sort((a, b) => a.name.localeCompare(b.name));
  saveListSortMode("bookmovie", "az", bookmovie);
  renderBookMovie(bookmovieSearch.value);
});

document.getElementById("btn-sort-za-bookmovie").addEventListener("click", () => {
  bookmovie.sort((a, b) => b.name.localeCompare(a.name));
  saveListSortMode("bookmovie", "za", bookmovie);
  renderBookMovie(bookmovieSearch.value);
});

playPauseBookMovieBtn.addEventListener("click", () => {
  if (!currentBookMovieId && bookmovie.length) return playBookMovieById(bookmovie[0].id);
  if (bookmoviePlayer.paused) {
    bookmoviePlayer.play();
    playPauseBookMovieBtn.textContent = "Pause";
  } else {
    bookmoviePlayer.pause();
    playPauseBookMovieBtn.textContent = "Play";
  }
});

nextBookMovieBtn.addEventListener("click", () => playNextBookMovie());

prevBookMovieBtn.addEventListener("click", () => playPrevBookMovie());

toggleRepeatBookMovieBtn.addEventListener("click", () => {
  bookmovieRepeat = !bookmovieRepeat;
  bookmoviePlayer.loop = bookmovieRepeat;
  toggleRepeatBookMovieBtn.textContent = `Repeat: ${bookmovieRepeat ? "On" : "Off"}`;
});

bookmoviePlayer.addEventListener("timeupdate", () => {
  if (!bookmoviePlayer.duration) return;
  bookmovieProgress.value = bookmoviePlayer.currentTime / bookmoviePlayer.duration * 100;
  updateRangeFill(bookmovieProgress);
  bookmovieCurrentTimeEl.textContent = formatTime(bookmoviePlayer.currentTime);
  bookmovieDurationEl.textContent = formatTime(bookmoviePlayer.duration);
  if (currentBookMovieId !== null) {
    const now = Date.now();
    if (now - lastBookMoviePositionSave > POSITION_SAVE_INTERVAL) {
      lastBookMoviePositionSave = now;
      bookmoviePositions[currentBookMovieId] = bookmoviePlayer.currentTime;
      appSet("bookmoviePositions", bookmoviePositions);
    }
  }
});

bookmovieProgress.addEventListener("input", () => {
  if (bookmoviePlayer.duration) bookmoviePlayer.currentTime = bookmovieProgress.value / 100 * bookmoviePlayer.duration;
  updateRangeFill(bookmovieProgress);
});

bookmoviePlayer.addEventListener("pause", () => {
  if (currentBookMovieId !== null && bookmoviePlayer.duration) {
    bookmoviePositions[currentBookMovieId] = bookmoviePlayer.currentTime;
    appSet("bookmoviePositions", bookmoviePositions);
  }
});

bookmoviePlayer.addEventListener("ended", () => {
  if (currentBookMovieId !== null) {
    delete bookmoviePositions[currentBookMovieId];
    appSet("bookmoviePositions", bookmoviePositions);
  }
  playNextBookMovie();
});

document.getElementById("forward-10-bookmovie").addEventListener("click", () => {
  bookmoviePlayer.currentTime += 10;
});

document.getElementById("rewind-10-bookmovie").addEventListener("click", () => {
  bookmoviePlayer.currentTime = Math.max(0, bookmoviePlayer.currentTime - 10);
});

function bookmoviePlaylistCtx() {
  return {
    playlistsObj: bookmoviePlaylists,
    metaObj: bookmoviePlaylistMeta,
    mediaArray: () => bookmovie,
    historyType: "bookmovie",
    listEl: bookmoviePlaylistsEl,
    toolbarEl: bookmoviePlaylistToolbarEl,
    tracksEl: playlistBookMovie,
    headerEl: bookmoviePlaylistHeaderEl,
    titleEl: bookmoviePlaylistTitle,
    getCurrent: () => currentBookMoviePlaylist,
    setCurrent: v => {
      currentBookMoviePlaylist = v;
    },
    getSortMode: () => bookmoviePlaylistSortMode,
    setSortMode: v => {
      bookmoviePlaylistSortMode = v;
      appSet("bookmoviePlaylistSortMode", v);
    },
    saveFn: saveBookMoviePlaylists,
    saveMetaFn: saveBookMoviePlaylistMeta,
    renderNamesFn: renderBookMoviePlaylists,
    renderTracksFn: renderPlaylistBookMovie,
    selectFn: selectBookMoviePlaylist,
    playByIdFn: id => playBookMovieById(id),
    currentPlayingId: () => currentBookMovieId,
    setPlaying: v => {
      bookmoviePlaylistPlaying = v;
    }
  };
}

function renderBookMoviePlaylists() {
  renderPlaylistNamesGeneric(bookmoviePlaylistCtx());
}

function selectBookMoviePlaylist(name) {
  currentBookMoviePlaylist = name;
  bookmoviePlaylistTitle.textContent = isSmartPlaylist(name) ? smartPlaylistLabel(name) : name;
  renderPlaylistBookMovie();
  renderBookMoviePlaylists();
}

function renderPlaylistBookMovie() {
  renderPlaylistTracksGeneric(bookmoviePlaylistCtx());
}

function saveBookMoviePlaylists() {
  appSet("bookmoviePlaylists", bookmoviePlaylists);
}

function saveBookMoviePlaylistMeta() {
  appSet("bookmoviePlaylistMeta", bookmoviePlaylistMeta);
}

document.getElementById("btn-create-bookmovie-playlist").addEventListener("click", () => {
  const name = bookmoviePlaylistName.value.trim();
  if (!name || bookmoviePlaylists[name] || isSmartPlaylist(name)) return alert("Invalid or duplicate playlist name");
  bookmoviePlaylists[name] = [];
  getPlaylistMeta(bookmoviePlaylistMeta, name);
  bookmoviePlaylistName.value = "";
  renderBookMoviePlaylists();
  saveBookMoviePlaylists();
  saveBookMoviePlaylistMeta();
});

document.getElementById("btn-delete-bookmovie-playlist").addEventListener("click", () => {
  if (!currentBookMoviePlaylist || isSmartPlaylist(currentBookMoviePlaylist)) return alert("Select a playlist first");
  delete bookmoviePlaylists[currentBookMoviePlaylist];
  delete bookmoviePlaylistMeta[currentBookMoviePlaylist];
  currentBookMoviePlaylist = null;
  bookmoviePlaylistTitle.textContent = "Select a playlist";
  renderPlaylistBookMovie();
  renderBookMoviePlaylists();
  saveBookMoviePlaylists();
  saveBookMoviePlaylistMeta();
});

document.getElementById("btn-add-selected-bookmovie-to-playlist").addEventListener("click", () => {
  if (!currentBookMoviePlaylist || isSmartPlaylist(currentBookMoviePlaylist)) return alert("Select a playlist first");
  document.querySelectorAll("#bookmovie-list input[type=checkbox]:checked").forEach(cb => {
    const id = Number(cb.dataset.id);
    if (!bookmoviePlaylists[currentBookMoviePlaylist].includes(id)) bookmoviePlaylists[currentBookMoviePlaylist].push(id);
  });
  touchPlaylistMeta(bookmoviePlaylistMeta, currentBookMoviePlaylist);
  renderPlaylistBookMovie();
  renderBookMoviePlaylists();
  saveBookMoviePlaylists();
  saveBookMoviePlaylistMeta();
});

document.getElementById("btn-add-all-bookmovie-to-playlist").addEventListener("click", () => {
  if (!currentBookMoviePlaylist || isSmartPlaylist(currentBookMoviePlaylist)) return alert("Select a playlist first");
  bookmovie.forEach(item => {
    if (!bookmoviePlaylists[currentBookMoviePlaylist].includes(item.id)) bookmoviePlaylists[currentBookMoviePlaylist].push(item.id);
  });
  touchPlaylistMeta(bookmoviePlaylistMeta, currentBookMoviePlaylist);
  renderPlaylistBookMovie();
  renderBookMoviePlaylists();
  saveBookMoviePlaylists();
  saveBookMoviePlaylistMeta();
});

document.getElementById("btn-remove-bookmovie-from-playlist").addEventListener("click", () => {
  if (!currentBookMoviePlaylist || isSmartPlaylist(currentBookMoviePlaylist)) return;
  const toRemove = Array.from(playlistBookMovie.querySelectorAll("input[type=checkbox]:checked")).map(cb => Number(cb.dataset.id));
  bookmoviePlaylists[currentBookMoviePlaylist] = bookmoviePlaylists[currentBookMoviePlaylist].filter(id => !toRemove.includes(id));
  touchPlaylistMeta(bookmoviePlaylistMeta, currentBookMoviePlaylist);
  renderPlaylistBookMovie();
  renderBookMoviePlaylists();
  saveBookMoviePlaylists();
  saveBookMoviePlaylistMeta();
});

document.getElementById("btn-clear-bookmovie-playlist").addEventListener("click", () => {
  if (!currentBookMoviePlaylist || isSmartPlaylist(currentBookMoviePlaylist)) return;
  bookmoviePlaylists[currentBookMoviePlaylist] = [];
  touchPlaylistMeta(bookmoviePlaylistMeta, currentBookMoviePlaylist);
  renderPlaylistBookMovie();
  renderBookMoviePlaylists();
  saveBookMoviePlaylists();
  saveBookMoviePlaylistMeta();
});

document.getElementById("btn-play-bookmovie-playlist").addEventListener("click", () => {
  const ids = getActivePlaylistIds(bookmoviePlaylistCtx());
  if (!currentBookMoviePlaylist || !ids.length) return alert("Select a playlist with book movies");
  bookmoviePlaylistPlaying = true;
  playBookMovieById(ids[0]);
});

document.getElementById("btn-export-bookmovie-playlist").addEventListener("click", () => {
  exportPlaylistFile(currentBookMoviePlaylist, currentBookMoviePlaylist ? getActivePlaylistIds(bookmoviePlaylistCtx()) : null, bookmovie);
});

document.getElementById("bookmovie-playlist-import").addEventListener("change", async e => {
  const file = e.target.files[0];
  if (!file) return;
  try {
    await importPlaylistFile(file, bookmovieDB, "bookmovie", bookmovie, bookmoviePlaylists, saveBookMoviePlaylists, renderPlaylistBookMovie, renderBookMoviePlaylists, selectBookMoviePlaylist, bookmoviePlaylistMeta, saveBookMoviePlaylistMeta, "video");
  } finally {
    e.target.value = "";
  }
  renderBookMovie(bookmovieSearch.value);
});

PLAYLIST_FOLDER_IMPORT_HANDLERS["bookmovie-playlist-import"] = async (files, folderName) => {
  await importPlaylistFolder(files, folderName, bookmovieDB, "bookmovie", bookmovie, bookmoviePlaylists, saveBookMoviePlaylists, renderPlaylistBookMovie, renderBookMoviePlaylists, selectBookMoviePlaylist, bookmoviePlaylistMeta, saveBookMoviePlaylistMeta, "video");
  renderBookMovie(bookmovieSearch.value);
};

(function enablePlaylistPanelDrop(wrapId, isValidId, getCurrentName, addToPlaylist, saveFn, renderListFn, renderNamesFn) {
  const wrap = document.getElementById(wrapId);
  if (!wrap) return;
  wrap.addEventListener("dragover", e => {
    if (!getCurrentName() || !e.dataTransfer.types.includes("text/plain")) return;
    e.preventDefault();
    e.dataTransfer.dropEffect = "copy";
    wrap.classList.add("drag-over");
  });
  wrap.addEventListener("dragleave", e => {
    if (!wrap.contains(e.relatedTarget)) wrap.classList.remove("drag-over");
  });
  wrap.addEventListener("drop", e => {
    e.preventDefault();
    wrap.classList.remove("drag-over");
    const name = getCurrentName();
    if (!name) return;
    const id = Number(e.dataTransfer.getData("text/plain"));
    if (!id || !isValidId(id)) return;
    addToPlaylist(name, id);
    saveFn();
    renderListFn();
    renderNamesFn();
  });
})("playlist-bookmovie-wrap", id => !!bookmovie.find(d => d.id === id), () => currentBookMoviePlaylist, (name, id) => {
  if (!bookmoviePlaylists[name].includes(id)) bookmoviePlaylists[name].push(id);
}, saveBookMoviePlaylists, renderPlaylistBookMovie, renderBookMoviePlaylists);

let presentations = [];

let currentPresentationId = null;

let presentationsDB;

const presentationsSearch = document.getElementById("presentations-search");

const presentationsUpload = document.getElementById("presentations-upload");

const presentationsList = document.getElementById("presentations-list");

const presentationsCount = document.getElementById("presentations-count");

const currentPresentationDisplay = document.getElementById("current-presentation");

const presentationFrame = document.getElementById("presentation-frame");

let presentationsPlaylists = {};

let presentationsPlaylistMeta = {};

let currentPresentationsPlaylist = null;

let presentationsPlaylistSortMode = "name";

const presentationsPlaylistsEl = document.getElementById("presentations-playlists");

const presentationsPlaylistToolbarEl = document.getElementById("presentations-playlist-toolbar");

const presentationsPlaylistName = document.getElementById("presentations-playlist-name");

const playlistPresentations = document.getElementById("playlist-presentations");

const presentationsPlaylistTitle = document.getElementById("presentations-playlist-title");

const presentationsPlaylistHeaderEl = document.getElementById("presentations-playlist-header");

function openPresentationsDB() {
  return openTerminalDB("PresentationsPlayerDB", [ {
    name: "presentations"
  } ]);
}

async function loadPresentationsFromDB() {
  if (!presentationsDB || !currentUserId) {
    presentations.length = 0;
    renderPresentations(presentationsSearch.value);
    return;
  }
  const rows = await loadUserRecordsIndexed(presentationsDB, "presentations", currentUserId);
  presentations.length = 0;
  presentations.push(...rows);
  renderPresentations(presentationsSearch.value);
}

const presentationSlidesPanel = document.getElementById("presentation-slides-panel");

const presentationSlideStatus = document.getElementById("presentation-slide-status");

const presentationSlideCounter = document.getElementById("presentation-slide-counter");

const presentationDownloadBtn = document.getElementById("presentation-download-btn");

const presentationFormatBadge = document.getElementById("presentation-format-badge");

let presentationSlides = [];

let presentationSlideIndex = 0;

function presentationFormatFor(name) {
  const ext = (name.split(".").pop() || "").toLowerCase();
  if (ext === "pdf") return "pdf";
  if (ext === "pptx") return "pptx";
  if (ext === "ppt") return "ppt";
  return "other";
}

async function loadPptxSlideText(blob) {
  const zip = await JSZip.loadAsync(blob);
  const slidePaths = Object.keys(zip.files).filter(p => /^ppt\/slides\/slide\d+\.xml$/.test(p)).sort((a, b) => {
    const na = Number(a.match(/slide(\d+)\.xml/)[1]);
    const nb = Number(b.match(/slide(\d+)\.xml/)[1]);
    return na - nb;
  });
  const slides = [];
  for (const path of slidePaths) {
    const xml = await zip.file(path).async("string");
    const texts = [ ...xml.matchAll(/<a:t>([^<]*)<\/a:t>/g) ].map(m => m[1]);
    slides.push(texts.join(" ").trim() || "(No readable text on this slide)");
  }
  return slides;
}

function renderPresentationSlide() {
  if (!presentationSlides.length) {
    presentationSlideCounter.textContent = "";
    return;
  }
  presentationSlideStatus.textContent = presentationSlides[presentationSlideIndex];
  presentationSlideCounter.textContent = `Slide ${presentationSlideIndex + 1} of ${presentationSlides.length}`;
}

function renderPresentations(filter = "") {
  const f = filter.toLowerCase();
  const visible = presentations.filter(p => !f || p.name.toLowerCase().includes(f));
  renderListBatched(presentationsList, visible, presentation => {
    const li = document.createElement("li");
    if (presentation.id === currentPresentationId) li.classList.add("selected");
    const name = document.createElement("span");
    name.textContent = `${presentation.name} · ${presentationFormatFor(presentation.name).toUpperCase()}`;
    const viewBtn = document.createElement("button");
    viewBtn.textContent = "▶";
    viewBtn.className = "media-row-play-btn";
    viewBtn.addEventListener("click", () => viewPresentationById(presentation.id));
    const deleteBtn = document.createElement("button");
    deleteBtn.textContent = "✕";
    deleteBtn.addEventListener("click", () => deletePresentationById(presentation.id));
    li.append(name, viewBtn, deleteBtn);
    return li;
  });
  presentationsCount.textContent = `Total Presentations: ${presentations.length}`;
}

async function viewPresentationById(id) {
  const presentation = presentations.find(b => b.id === id);
  if (!presentation) return;
  currentPresentationId = id;
  const format = presentationFormatFor(presentation.name);
  presentationFormatBadge.textContent = format.toUpperCase();
  if (presentationFrame.dataset.url) {
    URL.revokeObjectURL(presentationFrame.dataset.url);
    delete presentationFrame.dataset.url;
  }
  if (presentationDownloadBtn.dataset.url) URL.revokeObjectURL(presentationDownloadBtn.dataset.url);
  let downloadUrl;
  try {
    downloadUrl = URL.createObjectURL(presentation.blob);
  } catch (err) {
    console.error("Failed to load this presentation", err);
    alert("Could not load this presentation.");
    return;
  }
  presentationDownloadBtn.href = downloadUrl;
  presentationDownloadBtn.dataset.url = downloadUrl;
  presentationDownloadBtn.download = presentation.name;
  if (format === "pdf") {
    presentationFrame.style.display = "";
    presentationSlidesPanel.style.display = "none";
    presentationFrame.src = downloadUrl;
    presentationFrame.dataset.url = downloadUrl;
  } else if (format === "pptx") {
    presentationFrame.style.display = "none";
    presentationFrame.removeAttribute("src");
    presentationSlidesPanel.style.display = "";
    presentationSlideStatus.textContent = "Reading slides…";
    presentationSlideCounter.textContent = "";
    try {
      presentationSlides = await loadPptxSlideText(presentation.blob);
      presentationSlideIndex = 0;
      renderPresentationSlide();
    } catch (err) {
      console.error("Failed to read this presentation", err);
      presentationSlides = [];
      presentationSlideStatus.textContent = "Could not read slide content from this file. Use Download to open it in PowerPoint.";
    }
  } else {
    presentationFrame.style.display = "none";
    presentationFrame.removeAttribute("src");
    presentationSlidesPanel.style.display = "";
    presentationSlides = [];
    presentationSlideCounter.textContent = "";
    presentationSlideStatus.textContent = format === "ppt" ? "This legacy .ppt format can't be previewed in-browser. Use Download to open it in PowerPoint." : "This file format can't be previewed in-browser. Use Download to open it in another application.";
  }
  currentPresentationDisplay.textContent = presentation.name;
  renderPresentations(presentationsSearch.value);
}

function closePresentation() {
  currentPresentationId = null;
  if (presentationFrame.dataset.url) {
    URL.revokeObjectURL(presentationFrame.dataset.url);
    delete presentationFrame.dataset.url;
  }
  presentationFrame.removeAttribute("src");
  presentationFrame.style.display = "";
  presentationSlidesPanel.style.display = "none";
  presentationSlides = [];
  presentationSlideIndex = 0;
  presentationSlideStatus.textContent = "";
  presentationSlideCounter.textContent = "";
  presentationFormatBadge.textContent = "";
  if (presentationDownloadBtn.dataset.url) {
    URL.revokeObjectURL(presentationDownloadBtn.dataset.url);
    delete presentationDownloadBtn.dataset.url;
  }
  presentationDownloadBtn.removeAttribute("href");
  currentPresentationDisplay.textContent = "No presentation selected";
  renderPresentations(presentationsSearch.value);
}

document.getElementById("presentation-slide-prev").addEventListener("click", () => {
  if (!presentationSlides.length) return;
  presentationSlideIndex = presentationSlideIndex > 0 ? presentationSlideIndex - 1 : presentationSlides.length - 1;
  renderPresentationSlide();
});

document.getElementById("presentation-slide-next").addEventListener("click", () => {
  if (!presentationSlides.length) return;
  presentationSlideIndex = (presentationSlideIndex + 1) % presentationSlides.length;
  renderPresentationSlide();
});

function deletePresentationById(id) {
  if (!presentationsDB) return;
  if (!confirm("Delete this presentation?")) return;
  const tx = presentationsDB.transaction("presentations", "readwrite");
  tx.objectStore("presentations").delete(id);
  tx.oncomplete = () => {
    if (currentPresentationId === id) closePresentation();
    loadPresentationsFromDB();
  };
}

presentationsUpload.addEventListener("change", async e => {
  if (!presentationsDB || !currentUserId) return;
  const rawFiles = [ ...e.target.files ];
  if (!rawFiles.length) return;
  const files = filterUploadedMediaFiles(rawFiles, "presentation");
  if (!files.length) {
    presentationsUpload.value = "";
    return;
  }
  const existingKeys = new Set(presentations.map(b => `${b.name.toLowerCase()}|${b.blob.size}`));
  const newFiles = files.filter(f => !existingKeys.has(`${f.name.toLowerCase()}|${f.size}`));
  const skippedCount = files.length - newFiles.length;
  if (!newFiles.length) {
    presentationsUpload.value = "";
    if (skippedCount) alert(`Skipped ${skippedCount} duplicate presentation(s) already in your library.`);
    return;
  }
  const tx = presentationsDB.transaction("presentations", "readwrite");
  const store = tx.objectStore("presentations");
  newFiles.forEach(file => {
    store.add({
      name: file.name,
      blob: file,
      userId: currentUserId
    });
  });
  tx.oncomplete = () => {
    presentationsUpload.value = "";
    loadPresentationsFromDB();
    if (skippedCount) alert(`Added ${newFiles.length} presentation(s). Skipped ${skippedCount} duplicate(s).`);
  };
  tx.onerror = () => {
    console.error("Failed to save uploaded presentation(s)", tx.error);
    alert("Could not save the uploaded presentation file(s).");
  };
});

presentationsSearch.addEventListener("input", debounce(() => renderPresentations(presentationsSearch.value)));

document.getElementById("btn-close-presentation").addEventListener("click", closePresentation);

document.getElementById("btn-fullscreen-presentation").addEventListener("click", () => {
  if (presentationFrame.requestFullscreen) presentationFrame.requestFullscreen();
});

function presentationsPlaylistCtx() {
  return {
    playlistsObj: presentationsPlaylists,
    metaObj: presentationsPlaylistMeta,
    mediaArray: () => presentations,
    historyType: "presentations",
    listEl: presentationsPlaylistsEl,
    toolbarEl: presentationsPlaylistToolbarEl,
    tracksEl: playlistPresentations,
    headerEl: presentationsPlaylistHeaderEl,
    titleEl: presentationsPlaylistTitle,
    getCurrent: () => currentPresentationsPlaylist,
    setCurrent: v => {
      currentPresentationsPlaylist = v;
    },
    getSortMode: () => presentationsPlaylistSortMode,
    setSortMode: v => {
      presentationsPlaylistSortMode = v;
      appSet("presentationsPlaylistSortMode", v);
    },
    saveFn: savePresentationsPlaylists,
    saveMetaFn: savePresentationsPlaylistMeta,
    renderNamesFn: renderPresentationsPlaylists,
    renderTracksFn: renderPlaylistPresentations,
    selectFn: selectPresentationsPlaylist,
    playByIdFn: id => viewPresentationById(id),
    currentPlayingId: () => currentPresentationId,
    setPlaying: () => {}
  };
}

function renderPresentationsPlaylists() {
  renderPlaylistNamesGeneric(presentationsPlaylistCtx());
}

function selectPresentationsPlaylist(name) {
  currentPresentationsPlaylist = name;
  presentationsPlaylistTitle.textContent = isSmartPlaylist(name) ? smartPlaylistLabel(name) : name;
  renderPlaylistPresentations();
  renderPresentationsPlaylists();
}

function renderPlaylistPresentations() {
  renderPlaylistTracksGeneric(presentationsPlaylistCtx());
}

function savePresentationsPlaylists() {
  appSet("presentationsPlaylists", presentationsPlaylists);
}

function savePresentationsPlaylistMeta() {
  appSet("presentationsPlaylistMeta", presentationsPlaylistMeta);
}

document.getElementById("btn-create-presentations-playlist").addEventListener("click", () => {
  const name = presentationsPlaylistName.value.trim();
  if (!name || presentationsPlaylists[name] || isSmartPlaylist(name)) return alert("Invalid or duplicate playlist name");
  presentationsPlaylists[name] = [];
  getPlaylistMeta(presentationsPlaylistMeta, name);
  presentationsPlaylistName.value = "";
  renderPresentationsPlaylists();
  savePresentationsPlaylists();
  savePresentationsPlaylistMeta();
});

document.getElementById("btn-delete-presentations-playlist").addEventListener("click", () => {
  if (!currentPresentationsPlaylist || isSmartPlaylist(currentPresentationsPlaylist)) return alert("Select a playlist first");
  delete presentationsPlaylists[currentPresentationsPlaylist];
  delete presentationsPlaylistMeta[currentPresentationsPlaylist];
  currentPresentationsPlaylist = null;
  presentationsPlaylistTitle.textContent = "Select a playlist";
  renderPlaylistPresentations();
  renderPresentationsPlaylists();
  savePresentationsPlaylists();
  savePresentationsPlaylistMeta();
});

document.getElementById("btn-add-selected-presentations-to-playlist").addEventListener("click", () => {
  if (!currentPresentationsPlaylist || isSmartPlaylist(currentPresentationsPlaylist)) return alert("Select a playlist first");
  document.querySelectorAll("#presentations-list input[type=checkbox]:checked").forEach(cb => {
    const id = Number(cb.dataset.id);
    if (!presentationsPlaylists[currentPresentationsPlaylist].includes(id)) presentationsPlaylists[currentPresentationsPlaylist].push(id);
  });
  touchPlaylistMeta(presentationsPlaylistMeta, currentPresentationsPlaylist);
  renderPlaylistPresentations();
  renderPresentationsPlaylists();
  savePresentationsPlaylists();
  savePresentationsPlaylistMeta();
});

document.getElementById("btn-add-all-presentations-to-playlist").addEventListener("click", () => {
  if (!currentPresentationsPlaylist || isSmartPlaylist(currentPresentationsPlaylist)) return alert("Select a playlist first");
  presentations.forEach(b => {
    if (!presentationsPlaylists[currentPresentationsPlaylist].includes(b.id)) presentationsPlaylists[currentPresentationsPlaylist].push(b.id);
  });
  touchPlaylistMeta(presentationsPlaylistMeta, currentPresentationsPlaylist);
  renderPlaylistPresentations();
  renderPresentationsPlaylists();
  savePresentationsPlaylists();
  savePresentationsPlaylistMeta();
});

document.getElementById("btn-remove-presentations-from-playlist").addEventListener("click", () => {
  if (!currentPresentationsPlaylist || isSmartPlaylist(currentPresentationsPlaylist)) return;
  const toRemove = Array.from(playlistPresentations.querySelectorAll("input[type=checkbox]:checked")).map(cb => Number(cb.dataset.id));
  presentationsPlaylists[currentPresentationsPlaylist] = presentationsPlaylists[currentPresentationsPlaylist].filter(id => !toRemove.includes(id));
  touchPlaylistMeta(presentationsPlaylistMeta, currentPresentationsPlaylist);
  renderPlaylistPresentations();
  renderPresentationsPlaylists();
  savePresentationsPlaylists();
  savePresentationsPlaylistMeta();
});

document.getElementById("btn-clear-presentations-playlist").addEventListener("click", () => {
  if (!currentPresentationsPlaylist || isSmartPlaylist(currentPresentationsPlaylist)) return;
  presentationsPlaylists[currentPresentationsPlaylist] = [];
  touchPlaylistMeta(presentationsPlaylistMeta, currentPresentationsPlaylist);
  renderPlaylistPresentations();
  renderPresentationsPlaylists();
  savePresentationsPlaylists();
  savePresentationsPlaylistMeta();
});

document.getElementById("btn-play-presentations-playlist").addEventListener("click", () => {
  const ids = getActivePlaylistIds(presentationsPlaylistCtx());
  if (!currentPresentationsPlaylist || !ids.length) return alert("Select a playlist with presentations");
  viewPresentationById(ids[0]);
});

document.getElementById("btn-export-presentations-playlist").addEventListener("click", () => {
  exportPlaylistFile(currentPresentationsPlaylist, currentPresentationsPlaylist ? getActivePlaylistIds(presentationsPlaylistCtx()) : null, presentations);
});

document.getElementById("presentations-playlist-import").addEventListener("change", async e => {
  const file = e.target.files[0];
  if (!file) return;
  try {
    await importPlaylistFile(file, presentationsDB, "presentations", presentations, presentationsPlaylists, savePresentationsPlaylists, renderPlaylistPresentations, renderPresentationsPlaylists, selectPresentationsPlaylist, presentationsPlaylistMeta, savePresentationsPlaylistMeta, "presentation");
  } finally {
    e.target.value = "";
  }
  renderPresentations(presentationsSearch.value);
});

PLAYLIST_FOLDER_IMPORT_HANDLERS["presentations-playlist-import"] = async (files, folderName) => {
  await importPlaylistFolder(files, folderName, presentationsDB, "presentations", presentations, presentationsPlaylists, savePresentationsPlaylists, renderPlaylistPresentations, renderPresentationsPlaylists, selectPresentationsPlaylist, presentationsPlaylistMeta, savePresentationsPlaylistMeta, "presentation");
  renderPresentations(presentationsSearch.value);
};

(function enablePlaylistPanelDrop(wrapId, isValidId, getCurrentName, addToPlaylist, saveFn, renderListFn, renderNamesFn) {
  const wrap = document.getElementById(wrapId);
  if (!wrap) return;
  wrap.addEventListener("dragover", e => {
    if (!getCurrentName() || !e.dataTransfer.types.includes("text/plain")) return;
    e.preventDefault();
    e.dataTransfer.dropEffect = "copy";
    wrap.classList.add("drag-over");
  });
  wrap.addEventListener("dragleave", e => {
    if (!wrap.contains(e.relatedTarget)) wrap.classList.remove("drag-over");
  });
  wrap.addEventListener("drop", e => {
    e.preventDefault();
    wrap.classList.remove("drag-over");
    const name = getCurrentName();
    if (!name) return;
    const id = Number(e.dataTransfer.getData("text/plain"));
    if (!id || !isValidId(id)) return;
    addToPlaylist(name, id);
    saveFn();
    renderListFn();
    renderNamesFn();
  });
})("playlist-presentations-wrap", id => !!presentations.find(b => b.id === id), () => currentPresentationsPlaylist, (name, id) => {
  if (!presentationsPlaylists[name].includes(id)) presentationsPlaylists[name].push(id);
}, savePresentationsPlaylists, renderPlaylistPresentations, renderPresentationsPlaylists);

let bookmarks = [];

let bookmarkDB;

let bookmarkSortMode = "newest";

let editingBookmarkId = null;

let selectedBookmarkId = null;

let bookmarkRecent = [];

let bookmarkCollections = {};

let currentBookmarkCollection = null;

const bookmarkTitleInput = document.getElementById("bookmark-title-input");

const bookmarkUrlInput = document.getElementById("bookmark-url-input");

const bookmarkNotesInput = document.getElementById("bookmark-notes-input");

const bookmarkAddBtn = document.getElementById("bookmark-add-btn");

const bookmarkFormStatus = document.getElementById("bookmark-form-status");

const bookmarkSearch = document.getElementById("bookmark-search");

const bookmarkList = document.getElementById("bookmark-list");

const bookmarkCount = document.getElementById("bookmark-count");

const bookmarkSortSelect = document.getElementById("bookmark-sort-select");

const selectAllBookmarksCheckbox = document.getElementById("select-all-bookmarks");

const deleteSelectedBookmarksBtn = document.getElementById("btn-delete-selected-bookmarks");

const bookmarkCollectionName = document.getElementById("bookmark-collection-name");

const bookmarkCollectionsEl = document.getElementById("bookmark-collections");

const bookmarkCollectionTitle = document.getElementById("bookmark-collection-title");

const collectionBookmarksEl = document.getElementById("collection-bookmarks");

const bookmarkRecentList = document.getElementById("bookmark-recent-list");

const bookmarkHistoryList = document.getElementById("bookmark-history-list");

const currentBookmarkDisplay = document.getElementById("current-bookmark");

const bookmarkPreviewFavicon = document.getElementById("bookmark-preview-favicon");

const bookmarkPreviewLink = document.getElementById("bookmark-preview-link");

const bookmarkPreviewUrl = document.getElementById("bookmark-preview-url");

const bookmarkPreviewNotes = document.getElementById("bookmark-preview-notes");

const bookmarkPreviewBody = document.querySelector(".bookmark-preview-body");

const bookmarkPreviewOpenBtn = document.getElementById("bookmark-preview-open");

const bookmarkPreviewCopyBtn = document.getElementById("bookmark-preview-copy");

const bookmarkPreviewEditBtn = document.getElementById("bookmark-preview-edit");

const bookmarkPreviewDeleteBtn = document.getElementById("bookmark-preview-delete");

function openBookmarkDB() {
  return openTerminalDB("BookmarkManagerDB", [ {
    name: "bookmarks"
  } ]);
}

async function loadBookmarksFromDB() {
  if (!bookmarkDB || !currentUserId) {
    bookmarks.length = 0;
    renderBookmarks(bookmarkSearch ? bookmarkSearch.value : "");
    return;
  }
  const rows = await loadUserRecordsIndexed(bookmarkDB, "bookmarks", currentUserId);
  bookmarks.length = 0;
  bookmarks.push(...rows);
  applyBookmarkSort();
  renderBookmarks(bookmarkSearch ? bookmarkSearch.value : "");
}

function normalizeBookmarkUrl(raw) {
  const trimmed = raw.trim();
  if (!trimmed) return "";
  if (/^https?:\/\//i.test(trimmed)) return trimmed;
  return `https://${trimmed}`;
}

function applyBookmarkSort() {
  if (bookmarkSortMode === "az") {
    bookmarks.sort((a, b) => a.title.localeCompare(b.title));
  } else if (bookmarkSortMode === "za") {
    bookmarks.sort((a, b) => b.title.localeCompare(a.title));
  } else if (bookmarkSortMode === "oldest") {
    bookmarks.sort((a, b) => a.createdAt - b.createdAt);
  } else {
    bookmarks.sort((a, b) => b.createdAt - a.createdAt);
  }
}

function domainLetterFor(item) {
  try {
    return new URL(item.url).hostname.replace(/^www\./, "").charAt(0).toUpperCase() || "?";
  } catch {
    return (item.title || "?").charAt(0).toUpperCase();
  }
}

function applyFaviconImage(el, item) {
  if (!el) return;
  el.classList.remove("has-favicon-img");
  el.style.backgroundImage = "";
}

function renderBookmarks(filter = "") {
  if (!bookmarkList) return;
  const f = filter.toLowerCase();
  const visible = bookmarks.filter(item => !f || item.title.toLowerCase().includes(f) || item.url.toLowerCase().includes(f) || (item.notes || "").toLowerCase().includes(f));
  if (visible.length === 0) {
    bookmarkList.innerHTML = "";
    const emptyLi = document.createElement("li");
    emptyLi.className = "bookmark-empty-state";
    emptyLi.textContent = bookmarks.length === 0 ? "No bookmarks yet — save your first link above." : "No bookmarks match your search.";
    bookmarkList.appendChild(emptyLi);
  } else {
    renderListBatched(bookmarkList, visible, item => buildBookmarkRow(item));
  }
  if (bookmarkCount) bookmarkCount.textContent = `${bookmarks.length}`;
  if (selectAllBookmarksCheckbox) selectAllBookmarksCheckbox.checked = false;
}

function buildBookmarkRow(item) {
  const li = document.createElement("li");
  li.className = "bookmark-row";
  li.dataset.id = item.id;
  if (item.id === selectedBookmarkId) li.classList.add("selected");
  if (editingBookmarkId === item.id) {
    const titleEdit = document.createElement("input");
    titleEdit.type = "text";
    titleEdit.value = item.title;
    titleEdit.className = "bookmark-edit-input";
    const urlEdit = document.createElement("input");
    urlEdit.type = "text";
    urlEdit.value = item.url;
    urlEdit.className = "bookmark-edit-input";
    const notesEdit = document.createElement("input");
    notesEdit.type = "text";
    notesEdit.value = item.notes || "";
    notesEdit.placeholder = "Notes (optional)";
    notesEdit.className = "bookmark-edit-input";
    const saveBtn = document.createElement("button");
    saveBtn.textContent = "✔ Save";
    saveBtn.className = "action-button action-button--primary";
    saveBtn.addEventListener("click", () => {
      const newTitle = titleEdit.value.trim();
      const newUrl = normalizeBookmarkUrl(urlEdit.value);
      if (!newTitle || !newUrl) return alert("Title and URL are required.");
      item.title = newTitle;
      item.url = newUrl;
      item.notes = notesEdit.value.trim();
      saveBookmarkUpdate(item);
      editingBookmarkId = null;
      renderBookmarks(bookmarkSearch ? bookmarkSearch.value : "");
      if (selectedBookmarkId === item.id) renderBookmarkPreview();
    });
    const cancelBtn = document.createElement("button");
    cancelBtn.textContent = "Cancel";
    cancelBtn.className = "action-button";
    cancelBtn.addEventListener("click", () => {
      editingBookmarkId = null;
      renderBookmarks(bookmarkSearch ? bookmarkSearch.value : "");
    });
    li.append(titleEdit, urlEdit, notesEdit, saveBtn, cancelBtn);
  } else {
    const cb = document.createElement("input");
    cb.type = "checkbox";
    cb.className = "bookmark-select-cb";
    cb.dataset.id = item.id;
    cb.addEventListener("change", () => {
      if (selectAllBookmarksCheckbox) {
        const allChecked = Array.from(bookmarkList.querySelectorAll("input.bookmark-select-cb")).every(box => box.checked);
        selectAllBookmarksCheckbox.checked = allChecked;
      }
    });
    const favicon = document.createElement("span");
    favicon.className = "bookmark-favicon";
    favicon.setAttribute("data-letter", domainLetterFor(item));
    favicon.setAttribute("aria-hidden", "true");
    applyFaviconImage(favicon, item);
    const info = document.createElement("div");
    info.className = "bookmark-info";
    const titleLink = document.createElement("a");
    titleLink.href = item.url;
    titleLink.target = "_blank";
    titleLink.rel = "noopener noreferrer";
    titleLink.className = "bookmark-title-link";
    titleLink.textContent = item.title;
    titleLink.addEventListener("click", () => recordPlay("bookmark", item.title, (() => {
      try {
        return new URL(item.url).hostname;
      } catch {
        return "Bookmarks";
      }
    })()));
    const urlSpan = document.createElement("span");
    urlSpan.className = "bookmark-url";
    urlSpan.textContent = item.url;
    info.append(titleLink, urlSpan);
    if (item.notes) {
      const notesSpan = document.createElement("span");
      notesSpan.className = "bookmark-notes";
      notesSpan.textContent = item.notes;
      info.append(notesSpan);
    }
    const openBtn = document.createElement("button");
    openBtn.textContent = "↗ Open";
    openBtn.addEventListener("click", () => openBookmarkItem(item));
    const editBtn = document.createElement("button");
    editBtn.textContent = "✎ Edit";
    editBtn.addEventListener("click", () => {
      editingBookmarkId = item.id;
      renderBookmarks(bookmarkSearch ? bookmarkSearch.value : "");
    });
    const deleteBtn = document.createElement("button");
    deleteBtn.textContent = "✕";
    deleteBtn.addEventListener("click", () => deleteBookmarkById(item.id));
    li.append(cb, favicon, info, openBtn, editBtn, deleteBtn);
    li.addEventListener("click", e => {
      if (e.target === cb || e.target.tagName === "BUTTON" || e.target.tagName === "A") return;
      selectBookmark(item.id);
    });
  }
  return li;
}

function saveBookmarkUpdate(item) {
  if (!bookmarkDB) return;
  const tx = bookmarkDB.transaction("bookmarks", "readwrite");
  tx.objectStore("bookmarks").put(item);
}

function openBookmarkItem(item) {
  window.open(item.url, "_blank", "noopener,noreferrer");
  recordPlay("bookmark", item.title, (() => {
    try {
      return new URL(item.url).hostname;
    } catch {
      return "Bookmarks";
    }
  })());
}

function selectBookmark(id) {
  selectedBookmarkId = id;
  bookmarkList.querySelectorAll(".bookmark-row").forEach(row => {
    row.classList.toggle("selected", Number(row.dataset.id) === id);
  });
  renderBookmarkPreview();
}

function renderBookmarkPreview() {
  const item = bookmarks.find(b => b.id === selectedBookmarkId);
  if (!item) {
    if (currentBookmarkDisplay) currentBookmarkDisplay.textContent = "No bookmark selected";
    if (bookmarkPreviewBody) bookmarkPreviewBody.classList.add("bookmark-preview-body--empty");
    if (bookmarkPreviewFavicon) {
      bookmarkPreviewFavicon.setAttribute("data-letter", "?");
      bookmarkPreviewFavicon.classList.remove("has-favicon-img");
      bookmarkPreviewFavicon.style.backgroundImage = "";
    }
    if (bookmarkPreviewLink) {
      bookmarkPreviewLink.textContent = "Select a bookmark from the list to preview it here";
      bookmarkPreviewLink.removeAttribute("href");
    }
    if (bookmarkPreviewUrl) bookmarkPreviewUrl.textContent = "";
    if (bookmarkPreviewNotes) bookmarkPreviewNotes.textContent = "";
    return;
  }
  if (bookmarkPreviewBody) bookmarkPreviewBody.classList.remove("bookmark-preview-body--empty");
  if (currentBookmarkDisplay) currentBookmarkDisplay.textContent = item.title;
  if (bookmarkPreviewFavicon) {
    bookmarkPreviewFavicon.setAttribute("data-letter", domainLetterFor(item));
    applyFaviconImage(bookmarkPreviewFavicon, item);
  }
  if (bookmarkPreviewLink) {
    bookmarkPreviewLink.textContent = item.title;
    bookmarkPreviewLink.href = item.url;
  }
  if (bookmarkPreviewUrl) bookmarkPreviewUrl.textContent = item.url;
  if (bookmarkPreviewNotes) bookmarkPreviewNotes.textContent = item.notes || "";
}

function deleteBookmarkById(id) {
  if (!bookmarkDB) return;
  if (!confirm("Delete this bookmark?")) return;
  const tx = bookmarkDB.transaction("bookmarks", "readwrite");
  tx.objectStore("bookmarks").delete(id);
  tx.oncomplete = () => {
    Object.keys(bookmarkCollections).forEach(name => {
      bookmarkCollections[name] = bookmarkCollections[name].filter(bid => bid !== id);
    });
    saveBookmarkCollections();
    bookmarkRecent = bookmarkRecent.filter(e => e.id !== id);
    saveBookmarkRecent();
    renderBookmarkRecent();
    if (selectedBookmarkId === id) selectedBookmarkId = null;
    loadBookmarksFromDB().then(() => {
      renderCollectionBookmarks();
      renderBookmarkCollections();
      renderBookmarkPreview();
    });
  };
}

if (bookmarkAddBtn) {
  bookmarkAddBtn.addEventListener("click", () => {
    if (!bookmarkDB || !currentUserId) return;
    const title = bookmarkTitleInput.value.trim();
    const url = normalizeBookmarkUrl(bookmarkUrlInput.value);
    const notes = bookmarkNotesInput.value.trim();
    if (!title || !bookmarkUrlInput.value.trim()) {
      if (bookmarkFormStatus) bookmarkFormStatus.textContent = "Title and URL are required.";
      return;
    }
    const normalizedNew = url.toLowerCase().replace(/\/$/, "");
    const dupe = bookmarks.find(b => b.url.toLowerCase().replace(/\/$/, "") === normalizedNew);
    if (dupe && !confirm(`This URL is already saved as "${dupe.title}". Save it again anyway?`)) {
      if (bookmarkFormStatus) bookmarkFormStatus.textContent = "Save cancelled — duplicate URL.";
      return;
    }
    const tx = bookmarkDB.transaction("bookmarks", "readwrite");
    const store = tx.objectStore("bookmarks");
    const req = store.add({
      title: title,
      url: url,
      notes: notes,
      userId: currentUserId,
      createdAt: Date.now()
    });
    tx.oncomplete = () => {
      bookmarkRecent = bookmarkRecent.concat([ {
        entryId: `b${req.result}_${Date.now()}_${Math.random().toString(36).slice(2)}`,
        id: req.result,
        name: title,
        addedAt: Date.now()
      } ]);
      saveBookmarkRecent();
      renderBookmarkRecent();
      bookmarkTitleInput.value = "";
      bookmarkUrlInput.value = "";
      bookmarkNotesInput.value = "";
      if (bookmarkFormStatus) bookmarkFormStatus.textContent = "Bookmark saved.";
      loadBookmarksFromDB();
    };
    tx.onerror = () => {
      if (bookmarkFormStatus) bookmarkFormStatus.textContent = "Failed to save bookmark.";
    };
  });
}

if (bookmarkSearch) {
  bookmarkSearch.addEventListener("input", debounce(() => renderBookmarks(bookmarkSearch.value)));
}

if (bookmarkTitleInput) {
  bookmarkTitleInput.addEventListener("keydown", e => {
    if (e.key === "Enter") bookmarkUrlInput.focus();
  });
}

if (bookmarkUrlInput) {
  bookmarkUrlInput.addEventListener("keydown", e => {
    if (e.key === "Enter") bookmarkNotesInput.focus();
  });
}

if (bookmarkNotesInput) {
  bookmarkNotesInput.addEventListener("keydown", e => {
    if (e.key === "Enter") bookmarkAddBtn?.click();
  });
}

if (bookmarkSortSelect) {
  bookmarkSortSelect.addEventListener("change", () => {
    bookmarkSortMode = bookmarkSortSelect.value;
    appSet("bookmarkSortMode", bookmarkSortMode);
    applyBookmarkSort();
    renderBookmarks(bookmarkSearch ? bookmarkSearch.value : "");
  });
}

function syncCustomDropdown(selectEl) {
  const wrapper = selectEl?.previousElementSibling;
  if (!wrapper || !wrapper.classList.contains("custom-dropdown")) return;
  const toggleValue = wrapper.querySelector(".custom-dropdown-value");
  const options = wrapper.querySelectorAll(".custom-dropdown-option");
  options.forEach(opt => {
    const isMatch = opt.dataset.value === selectEl.value;
    opt.classList.toggle("selected", isMatch);
    opt.setAttribute("aria-selected", isMatch ? "true" : "false");
    if (isMatch && toggleValue) toggleValue.textContent = opt.textContent;
  });
}

function initCustomDropdown(wrapper, selectEl) {
  if (!wrapper || !selectEl) return;
  const toggle = wrapper.querySelector(".custom-dropdown-toggle");
  const menu = wrapper.querySelector(".custom-dropdown-menu");
  const options = Array.from(wrapper.querySelectorAll(".custom-dropdown-option"));
  let activeIndex = options.findIndex(opt => opt.classList.contains("selected"));
  function closeMenu() {
    menu.hidden = true;
    toggle.setAttribute("aria-expanded", "false");
    wrapper.classList.remove("open");
  }
  function openMenu() {
    menu.hidden = false;
    toggle.setAttribute("aria-expanded", "true");
    wrapper.classList.add("open");
    activeIndex = options.findIndex(opt => opt.classList.contains("selected"));
    options.forEach(opt => opt.classList.remove("active"));
    if (options[activeIndex]) options[activeIndex].classList.add("active");
    menu.focus();
  }
  function selectOption(opt) {
    selectEl.value = opt.dataset.value;
    selectEl.dispatchEvent(new Event("change", {
      bubbles: true
    }));
    syncCustomDropdown(selectEl);
    closeMenu();
    toggle.focus();
  }
  toggle.addEventListener("click", () => {
    if (menu.hidden) openMenu(); else closeMenu();
  });
  toggle.addEventListener("keydown", e => {
    if (e.key === "ArrowDown" || e.key === "Enter" || e.key === " ") {
      e.preventDefault();
      if (menu.hidden) openMenu(); else selectOption(options[activeIndex] || options[0]);
    } else if (e.key === "Escape") {
      closeMenu();
    }
  });
  options.forEach((opt, index) => {
    opt.addEventListener("click", () => selectOption(opt));
    opt.addEventListener("mouseenter", () => {
      options.forEach(o => o.classList.remove("active"));
      opt.classList.add("active");
      activeIndex = index;
    });
  });
  menu.addEventListener("keydown", e => {
    if (e.key === "ArrowDown") {
      e.preventDefault();
      activeIndex = Math.min(activeIndex + 1, options.length - 1);
      options.forEach(o => o.classList.remove("active"));
      options[activeIndex].classList.add("active");
      options[activeIndex].scrollIntoView({
        block: "nearest"
      });
    } else if (e.key === "ArrowUp") {
      e.preventDefault();
      activeIndex = Math.max(activeIndex - 1, 0);
      options.forEach(o => o.classList.remove("active"));
      options[activeIndex].classList.add("active");
      options[activeIndex].scrollIntoView({
        block: "nearest"
      });
    } else if (e.key === "Enter" || e.key === " ") {
      e.preventDefault();
      selectOption(options[activeIndex]);
    } else if (e.key === "Escape") {
      closeMenu();
      toggle.focus();
    } else if (e.key === "Tab") {
      closeMenu();
    }
  });
  document.addEventListener("click", e => {
    if (!wrapper.contains(e.target)) closeMenu();
  });
}

const bookmarkSortDropdown = document.getElementById("bookmark-sort-dropdown");

if (bookmarkSortDropdown && bookmarkSortSelect) {
  initCustomDropdown(bookmarkSortDropdown, bookmarkSortSelect);
}

if (selectAllBookmarksCheckbox) {
  selectAllBookmarksCheckbox.addEventListener("change", () => {
    bookmarkList.querySelectorAll("input.bookmark-select-cb").forEach(cb => {
      cb.checked = selectAllBookmarksCheckbox.checked;
    });
  });
}

if (deleteSelectedBookmarksBtn) {
  deleteSelectedBookmarksBtn.addEventListener("click", () => {
    if (!bookmarkDB) return alert("Database not ready");
    const selected = bookmarkList.querySelectorAll("input.bookmark-select-cb:checked");
    if (!selected.length) return alert("No bookmarks selected");
    if (!confirm(`Delete ${selected.length} selected bookmark(s)?`)) return;
    const idsToRemove = Array.from(selected).map(cb => Number(cb.dataset.id)).filter(id => !isNaN(id));
    const tx = bookmarkDB.transaction("bookmarks", "readwrite");
    const store = tx.objectStore("bookmarks");
    idsToRemove.forEach(id => store.delete(id));
    tx.oncomplete = () => {
      Object.keys(bookmarkCollections).forEach(name => {
        bookmarkCollections[name] = bookmarkCollections[name].filter(id => !idsToRemove.includes(id));
      });
      saveBookmarkCollections();
      bookmarkRecent = bookmarkRecent.filter(e => !idsToRemove.includes(e.id));
      saveBookmarkRecent();
      renderBookmarkRecent();
      if (idsToRemove.includes(selectedBookmarkId)) selectedBookmarkId = null;
      loadBookmarksFromDB().then(() => {
        renderCollectionBookmarks();
        renderBookmarkCollections();
        renderBookmarkPreview();
      });
    };
    tx.onerror = () => {
      console.error("Failed to delete selected bookmarks", tx.error);
      alert("Could not delete the selected bookmarks.");
    };
  });
}

function saveBookmarkRecent() {
  appSet("bookmarkRecent", bookmarkRecent);
}

function renderBookmarkRecent() {
  if (!bookmarkRecentList) return;
  bookmarkRecentList.innerHTML = "";
  const sorted = [ ...bookmarkRecent ].sort((a, b) => b.addedAt - a.addedAt);
  if (!sorted.length) {
    bookmarkRecentList.appendChild(buildHistoryRow({
      empty: true,
      title: "No recent uploads in Bookmark Terminal.",
      removeClass: "recent-remove-btn"
    }));
    return;
  }
  sorted.forEach(entry => {
    bookmarkRecentList.appendChild(buildHistoryRow({
      mediaType: "bookmark",
      title: entry.name,
      metaParts: [ {
        className: "history-timestamp",
        text: new Date(entry.addedAt).toLocaleString()
      } ],
      removeClass: "recent-remove-btn",
      onRemove: () => {
        bookmarkRecent = bookmarkRecent.filter(e => e.entryId !== entry.entryId);
        saveBookmarkRecent();
        renderBookmarkRecent();
      }
    }));
  });
}

document.getElementById("btn-clear-bookmark-recent")?.addEventListener("click", () => {
  bookmarkRecent = [];
  saveBookmarkRecent();
  renderBookmarkRecent();
});

function downloadBookmarkRecent() {
  const sorted = [ ...bookmarkRecent ].map(e => e.name).sort();
  const content = sorted.join("\n");
  const blob = new Blob([ content ], {
    type: "text/plain"
  });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = "bookmarks_recently_added.txt";
  a.click();
  URL.revokeObjectURL(url);
}

document.getElementById("btn-download-bookmark-recent")?.addEventListener("click", downloadBookmarkRecent);

function renderBookmarkHistory() {
  renderHistoryList(bookmarkHistoryList, "bookmark");
}

document.getElementById("btn-clear-bookmark-history")?.addEventListener("click", () => {
  if (!historyReady) return;
  historyData.play_log = historyData.play_log.filter(row => row.media_type !== "bookmark");
  saveHistoryBuffer();
  refreshHistoryCache();
  renderBookmarkHistory();
});

function downloadBookmarkHistory() {
  if (!historyReady) return;
  const names = [ ...new Set(historyData.play_log.filter(row => row.media_type === "bookmark").map(row => row.media_name)) ].sort();
  const content = names.join("\n");
  const blob = new Blob([ content ], {
    type: "text/plain"
  });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = "bookmarks_history.txt";
  a.click();
  URL.revokeObjectURL(url);
}

document.getElementById("btn-download-bookmark-history")?.addEventListener("click", downloadBookmarkHistory);

function saveBookmarkCollections() {
  appSet("bookmarkCollections", bookmarkCollections);
}

function renderBookmarkCollections() {
  if (!bookmarkCollectionsEl) return;
  bookmarkCollectionsEl.innerHTML = "";
  const names = Object.keys(bookmarkCollections).sort((a, b) => a.localeCompare(b));
  const collectionCountEl = document.getElementById("bookmark-collection-count");
  if (collectionCountEl) collectionCountEl.textContent = `${names.length}`;
  if (!names.length) {
    const emptyLi = document.createElement("li");
    emptyLi.className = "media-list-empty";
    emptyLi.textContent = "No collections yet — create one above.";
    bookmarkCollectionsEl.appendChild(emptyLi);
    return;
  }
  names.forEach(name => {
    const li = document.createElement("li");
    li.dataset.collectionName = name;
    if (name === currentBookmarkCollection) li.classList.add("selected");
    const nameEl = document.createElement("span");
    nameEl.className = "playlist-item-name";
    nameEl.textContent = name;
    const countEl = document.createElement("span");
    countEl.className = "playlist-item-count";
    countEl.textContent = (bookmarkCollections[name] || []).length;
    const renameBtn = document.createElement("button");
    renameBtn.className = "playlist-item-icon-btn";
    renameBtn.textContent = "✏️";
    renameBtn.title = "Rename collection";
    renameBtn.addEventListener("click", e => {
      e.stopPropagation();
      renameBookmarkCollection(name);
    });
    li.append(nameEl, countEl, renameBtn);
    li.addEventListener("click", () => selectBookmarkCollection(name));
    bookmarkCollectionsEl.appendChild(li);
  });
}

function renameBookmarkCollection(oldName) {
  const input = prompt("Rename collection to:", oldName);
  if (input === null) return;
  const trimmed = input.trim();
  if (!trimmed) return alert("Collection name cannot be empty.");
  if (trimmed === oldName) return;
  if (bookmarkCollections[trimmed]) return alert(`A collection named "${trimmed}" already exists.`);
  bookmarkCollections[trimmed] = bookmarkCollections[oldName];
  delete bookmarkCollections[oldName];
  if (currentBookmarkCollection === oldName) {
    currentBookmarkCollection = trimmed;
    if (bookmarkCollectionTitle) bookmarkCollectionTitle.textContent = trimmed;
  }
  saveBookmarkCollections();
  renderBookmarkCollections();
}

function selectBookmarkCollection(name) {
  currentBookmarkCollection = name;
  if (bookmarkCollectionTitle) bookmarkCollectionTitle.textContent = name;
  renderBookmarkCollections();
  renderCollectionBookmarks();
}

let collectionContentsSortMode = "";

function renderCollectionBookmarks() {
  if (!collectionBookmarksEl) return;
  collectionBookmarksEl.innerHTML = "";
  if (!currentBookmarkCollection) return;
  const ids = bookmarkCollections[currentBookmarkCollection] || [];
  if (!ids.length) {
    const emptyLi = document.createElement("li");
    emptyLi.className = "media-list-empty";
    emptyLi.textContent = "This collection is empty.";
    collectionBookmarksEl.appendChild(emptyLi);
    return;
  }
  const sortedIds = [ ...ids ];
  if (collectionContentsSortMode === "az" || collectionContentsSortMode === "za") {
    sortedIds.sort((a, b) => {
      const itemA = bookmarks.find(b2 => b2.id === a);
      const itemB = bookmarks.find(b2 => b2.id === b);
      const titleA = itemA ? itemA.title.toLowerCase() : "";
      const titleB = itemB ? itemB.title.toLowerCase() : "";
      return collectionContentsSortMode === "az" ? titleA.localeCompare(titleB) : titleB.localeCompare(titleA);
    });
  }
  sortedIds.forEach(id => {
    const item = bookmarks.find(b => b.id === id);
    if (!item) return;
    const li = document.createElement("li");
    li.dataset.id = id;
    const cb = document.createElement("input");
    cb.type = "checkbox";
    cb.dataset.id = id;
    const nameEl = document.createElement("span");
    nameEl.textContent = item.title;
    const openBtn = document.createElement("button");
    openBtn.textContent = "↗";
    openBtn.addEventListener("click", () => openBookmarkItem(item));
    li.append(cb, nameEl, openBtn);
    li.addEventListener("click", e => {
      if (e.target === cb || e.target.tagName === "BUTTON") return;
      selectBookmark(id);
    });
    collectionBookmarksEl.appendChild(li);
  });
}

document.getElementById("btn-sort-collection-az")?.addEventListener("click", () => {
  collectionContentsSortMode = "az";
  renderCollectionBookmarks();
});

document.getElementById("btn-sort-collection-za")?.addEventListener("click", () => {
  collectionContentsSortMode = "za";
  renderCollectionBookmarks();
});

document.getElementById("btn-create-bookmark-collection")?.addEventListener("click", () => {
  const name = bookmarkCollectionName.value.trim();
  if (!name || bookmarkCollections[name]) return alert("Invalid or duplicate collection name");
  bookmarkCollections[name] = [];
  bookmarkCollectionName.value = "";
  renderBookmarkCollections();
  saveBookmarkCollections();
});

document.getElementById("btn-delete-bookmark-collection")?.addEventListener("click", () => {
  if (!currentBookmarkCollection) return alert("Select a collection first");
  delete bookmarkCollections[currentBookmarkCollection];
  currentBookmarkCollection = null;
  if (bookmarkCollectionTitle) bookmarkCollectionTitle.textContent = "Select a collection";
  renderCollectionBookmarks();
  renderBookmarkCollections();
  saveBookmarkCollections();
});

document.getElementById("btn-add-selected-bookmarks-to-collection")?.addEventListener("click", () => {
  if (!currentBookmarkCollection) return alert("Select a collection first");
  document.querySelectorAll("#bookmark-list input.bookmark-select-cb:checked").forEach(cb => {
    const id = Number(cb.dataset.id);
    if (!bookmarkCollections[currentBookmarkCollection].includes(id)) bookmarkCollections[currentBookmarkCollection].push(id);
  });
  renderCollectionBookmarks();
  renderBookmarkCollections();
  saveBookmarkCollections();
});

document.getElementById("btn-add-all-bookmarks-to-collection")?.addEventListener("click", () => {
  if (!currentBookmarkCollection) return alert("Select a collection first");
  bookmarks.forEach(b => {
    if (!bookmarkCollections[currentBookmarkCollection].includes(b.id)) bookmarkCollections[currentBookmarkCollection].push(b.id);
  });
  renderCollectionBookmarks();
  renderBookmarkCollections();
  saveBookmarkCollections();
});

document.getElementById("btn-remove-bookmark-from-collection")?.addEventListener("click", () => {
  if (!currentBookmarkCollection) return;
  const toRemove = Array.from(collectionBookmarksEl.querySelectorAll("input[type=checkbox]:checked")).map(cb => Number(cb.dataset.id));
  bookmarkCollections[currentBookmarkCollection] = bookmarkCollections[currentBookmarkCollection].filter(id => !toRemove.includes(id));
  renderCollectionBookmarks();
  renderBookmarkCollections();
  saveBookmarkCollections();
});

document.getElementById("btn-clear-bookmark-collection")?.addEventListener("click", () => {
  if (!currentBookmarkCollection) return;
  bookmarkCollections[currentBookmarkCollection] = [];
  renderCollectionBookmarks();
  renderBookmarkCollections();
  saveBookmarkCollections();
});

document.getElementById("btn-open-bookmark-collection")?.addEventListener("click", () => {
  const ids = bookmarkCollections[currentBookmarkCollection] || [];
  if (!currentBookmarkCollection || !ids.length) return alert("Select a collection with bookmarks");
  if (ids.length > 6 && !confirm(`Open ${ids.length} links in new tabs?`)) return;
  ids.forEach(id => {
    const item = bookmarks.find(b => b.id === id);
    if (item) openBookmarkItem(item);
  });
});

function exportBookmarksToFile(items, filename) {
  const payload = {
    bookmarks: items.map(b => ({
      title: b.title,
      url: b.url,
      notes: b.notes || ""
    }))
  };
  const blob = new Blob([ JSON.stringify(payload, null, 2) ], {
    type: "application/json"
  });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = filename;
  a.click();
  URL.revokeObjectURL(url);
}

async function importBookmarksFromFile(file) {
  if (!bookmarkDB || !currentUserId) return alert("Database not ready");
  let payload;
  try {
    payload = JSON.parse(await file.text());
  } catch {
    return alert("That file is not a valid bookmarks export.");
  }
  const items = Array.isArray(payload) ? payload : Array.isArray(payload && payload.bookmarks) ? payload.bookmarks : null;
  if (!items) return alert("That file is not a valid bookmarks export.");
  const existingUrls = new Set(bookmarks.map(b => b.url.toLowerCase().replace(/\/$/, "")));
  const addedIds = [];
  let skipped = 0;
  for (const raw of items) {
    if (!raw || !raw.url) continue;
    const url = normalizeBookmarkUrl(String(raw.url));
    const key = url.toLowerCase().replace(/\/$/, "");
    if (!url || existingUrls.has(key)) {
      skipped++;
      continue;
    }
    const title = (raw.title || url).trim();
    const notes = (raw.notes || "").trim();
    const id = await new Promise(resolve => {
      const tx = bookmarkDB.transaction("bookmarks", "readwrite");
      const req = tx.objectStore("bookmarks").add({
        title: title,
        url: url,
        notes: notes,
        userId: currentUserId,
        createdAt: Date.now()
      });
      tx.oncomplete = () => resolve(req.result);
      tx.onerror = () => resolve(null);
    });
    if (id !== null) addedIds.push(id);
    existingUrls.add(key);
  }
  await loadBookmarksFromDB();
  renderCollectionBookmarks();
  renderBookmarkCollections();
  if (bookmarkFormStatus) bookmarkFormStatus.textContent = `Imported ${addedIds.length} bookmark(s)${skipped ? `, skipped ${skipped} duplicate(s)` : ""}.`;
  return addedIds;
}

document.getElementById("btn-export-bookmarks")?.addEventListener("click", () => {
  if (!bookmarks.length) return alert("No bookmarks to export.");
  exportBookmarksToFile(bookmarks, "bookmarks_export.json");
});

const bookmarkImportInput = document.getElementById("bookmark-import");

if (bookmarkImportInput) {
  bookmarkImportInput.addEventListener("change", async () => {
    const file = bookmarkImportInput.files[0];
    bookmarkImportInput.value = "";
    if (!file) return;
    await importBookmarksFromFile(file);
  });
}

document.getElementById("btn-export-bookmark-collection")?.addEventListener("click", () => {
  if (!currentBookmarkCollection) return alert("Select a collection first");
  const ids = bookmarkCollections[currentBookmarkCollection] || [];
  const items = ids.map(id => bookmarks.find(b => b.id === id)).filter(Boolean);
  if (!items.length) return alert("This collection is empty.");
  exportBookmarksToFile(items, `${currentBookmarkCollection.replace(/[^a-z0-9]+/gi, "_")}_collection.json`);
});

const bookmarkCollectionImportInput = document.getElementById("bookmark-collection-import");

if (bookmarkCollectionImportInput) {
  bookmarkCollectionImportInput.addEventListener("change", async () => {
    const file = bookmarkCollectionImportInput.files[0];
    bookmarkCollectionImportInput.value = "";
    if (!file) return;
    if (!currentBookmarkCollection) return alert("Select a collection first");
    const addedIds = await importBookmarksFromFile(file);
    if (!addedIds) return;
    addedIds.forEach(id => {
      if (!bookmarkCollections[currentBookmarkCollection].includes(id)) bookmarkCollections[currentBookmarkCollection].push(id);
    });
    saveBookmarkCollections();
    renderCollectionBookmarks();
    renderBookmarkCollections();
  });
}

if (bookmarkPreviewOpenBtn) {
  bookmarkPreviewOpenBtn.addEventListener("click", () => {
    const item = bookmarks.find(b => b.id === selectedBookmarkId);
    if (!item) return alert("Select a bookmark first");
    openBookmarkItem(item);
  });
}

if (bookmarkPreviewCopyBtn) {
  bookmarkPreviewCopyBtn.addEventListener("click", async () => {
    const item = bookmarks.find(b => b.id === selectedBookmarkId);
    if (!item) return alert("Select a bookmark first");
    try {
      await navigator.clipboard.writeText(item.url);
      bookmarkPreviewCopyBtn.textContent = "✔ Copied";
      setTimeout(() => bookmarkPreviewCopyBtn.textContent = "⧉ Copy URL", 1200);
    } catch {
      alert("Could not copy the URL.");
    }
  });
}

if (bookmarkPreviewEditBtn) {
  bookmarkPreviewEditBtn.addEventListener("click", () => {
    if (!selectedBookmarkId) return alert("Select a bookmark first");
    editingBookmarkId = selectedBookmarkId;
    renderBookmarks(bookmarkSearch ? bookmarkSearch.value : "");
    bookmarkList.querySelector(`.bookmark-row[data-id="${selectedBookmarkId}"]`)?.scrollIntoView({
      behavior: "smooth",
      block: "center"
    });
  });
}

if (bookmarkPreviewDeleteBtn) {
  bookmarkPreviewDeleteBtn.addEventListener("click", () => {
    if (!selectedBookmarkId) return alert("Select a bookmark first");
    deleteBookmarkById(selectedBookmarkId);
  });
}

(function() {
  function makeDraggable(panel, handle) {
    let offsetX = 0, offsetY = 0, dragging = false;
    handle.addEventListener("mousedown", e => {
      dragging = true;
      panel.classList.add("dragging");
      const rect = panel.getBoundingClientRect();
      offsetX = e.clientX - rect.left;
      offsetY = e.clientY - rect.top;
      panel.style.right = "auto";
      panel.style.bottom = "auto";
      panel.style.left = `${rect.left}px`;
      panel.style.top = `${rect.top}px`;
    });
    window.addEventListener("mousemove", e => {
      if (!dragging) return;
      panel.style.left = `${e.clientX - offsetX}px`;
      panel.style.top = `${e.clientY - offsetY}px`;
    });
    window.addEventListener("mouseup", () => {
      dragging = false;
      panel.classList.remove("dragging");
    });
  }
  function setupVideoFamilyMini(opts) {
    const {key: key, playerEl: playerEl, dockEl: dockEl, currentIdGetter: currentIdGetter, currentDisplayEl: currentDisplayEl, playPauseBtn: playPauseBtn, prevBtn: prevBtn, nextBtn: nextBtn, sourceLabel: sourceLabel, pageKey: pageKey} = opts;
    const mini = document.getElementById(`${key}-mini-player`);
    const toggleBtn = document.getElementById(`${key}-mini-player-toggle`);
    const closeBtn = document.getElementById(`mp-${key}-close`);
    const titleEl = document.getElementById(`mp-${key}-title`);
    const sourceEl = document.getElementById(`mp-${key}-source`);
    const progressEl = document.getElementById(`mp-${key}-progress`);
    const playBtnMini = document.getElementById(`mp-${key}-play`);
    const prevBtnMini = document.getElementById(`mp-${key}-prev`);
    const nextBtnMini = document.getElementById(`mp-${key}-next`);
    const rewindBtnMini = document.getElementById(`mp-${key}-rewind`);
    const forwardBtnMini = document.getElementById(`mp-${key}-forward`);
    const thumbEl = document.getElementById(`mp-${key}-thumb`);
    const handle = mini.querySelector(".mini-player-drag-handle");
    if (!mini || !toggleBtn) return null;
    const home = mini.parentElement;
    const placeholder = document.createElement("div");
    placeholder.className = "mini-player-thumb-placeholder";
    placeholder.textContent = "🎬";
    placeholder.style.display = "none";
    thumbEl.appendChild(placeholder);
    let isOn = false;
    let pipWindow = null;
    function moveEl(container, mini_) {
      container.appendChild(playerEl);
      playerEl.classList.toggle("video-player--mini", mini_);
      const showPlaceholder = mini_ && currentIdGetter() === null;
      playerEl.style.display = showPlaceholder ? "none" : "";
      placeholder.style.display = showPlaceholder ? "" : "none";
    }
    async function setState(on) {
      isOn = on;
      toggleBtn.classList.toggle("active-toggle", on);
      if (on) {
        moveEl(thumbEl, true);
        if (supportsDocPip) {
          try {
            pipWindow = await openDocPip(mini, home, () => {
              isOn = false;
              mini.classList.remove("show");
              toggleBtn.classList.remove("active-toggle");
              pipWindow = null;
              moveEl(dockEl, false);
            }, 360, 460);
            return;
          } catch (err) {
            console.error("Document Picture-in-Picture failed, falling back to floating panel", err);
          }
        }
        mini.classList.add("show");
      } else {
        if (pipWindow) {
          pipWindow.close();
          pipWindow = null;
        }
        mini.classList.remove("show");
        moveEl(dockEl, false);
      }
    }
    toggleBtn.addEventListener("click", () => {
      const turningOn = !isOn;
      if (turningOn) turnOffOtherMinis(key);
      setState(turningOn);
    });
    closeBtn.addEventListener("click", () => setState(false));
    playBtnMini.addEventListener("click", () => playPauseBtn.click());
    prevBtnMini.addEventListener("click", () => prevBtn.click());
    nextBtnMini.addEventListener("click", () => nextBtn.click());
    rewindBtnMini?.addEventListener("click", () => document.getElementById(`rewind-10-${key}`)?.click());
    forwardBtnMini?.addEventListener("click", () => document.getElementById(`forward-10-${key}`)?.click());
    progressEl.addEventListener("input", () => {
      if (playerEl.duration) playerEl.currentTime = progressEl.value / 100 * playerEl.duration;
      updateRangeFill(progressEl);
    });
    playerEl.addEventListener("timeupdate", () => {
      if (!playerEl.duration) return;
      progressEl.value = playerEl.currentTime / playerEl.duration * 100;
      updateRangeFill(progressEl);
    });
    playerEl.addEventListener("play", () => {
      playBtnMini.textContent = "⏸︎";
    });
    playerEl.addEventListener("pause", () => {
      playBtnMini.textContent = "▶︎";
    });
    new MutationObserver(() => {
      titleEl.textContent = currentDisplayEl.textContent;
      sourceEl.textContent = currentIdGetter() !== null ? sourceLabel : "";
    }).observe(currentDisplayEl, {
      childList: true,
      characterData: true,
      subtree: true
    });
    makeDraggable(mini, handle);
    registerMiniPlayer(key, () => setState(false), () => isOn);
    return {
      onPageEnter() {
        if (isOn) setState(false);
      }
    };
  }
  function setupSimpleMini(opts) {
    const {key: key, currentIdGetter: currentIdGetter, currentDisplayEl: currentDisplayEl, stopFn: stopFn, pageKey: pageKey} = opts;
    const mini = document.getElementById(`${key}-mini-player`);
    const toggleBtn = document.getElementById(`${key}-mini-player-toggle`);
    const closeBtn = document.getElementById(`mp-${key}-close`);
    const titleEl = document.getElementById(`mp-${key}-title`);
    const resumeBtn = document.getElementById(`mp-${key}-resume`);
    const stopBtn = document.getElementById(`mp-${key}-stop`);
    const handle = mini.querySelector(".mini-player-drag-handle");
    if (!mini || !toggleBtn) return null;
    const home = mini.parentElement;
    let isOn = false;
    let pipWindow = null;
    async function setState(on) {
      isOn = on;
      toggleBtn.classList.toggle("active-toggle", on);
      if (on) {
        if (supportsDocPip) {
          try {
            pipWindow = await openDocPip(mini, home, () => {
              isOn = false;
              mini.classList.remove("show");
              toggleBtn.classList.remove("active-toggle");
              pipWindow = null;
            }, 320, 180);
            return;
          } catch (err) {
            console.error("Document Picture-in-Picture failed, falling back to floating panel", err);
          }
        }
        mini.classList.add("show");
      } else {
        if (pipWindow) {
          pipWindow.close();
          pipWindow = null;
        }
        mini.classList.remove("show");
      }
    }
    toggleBtn.addEventListener("click", () => {
      const turningOn = !isOn;
      if (turningOn) turnOffOtherMinis(key);
      setState(turningOn);
    });
    closeBtn.addEventListener("click", () => setState(false));
    resumeBtn.addEventListener("click", () => {
      setState(false);
      showPage(pageKey);
    });
    stopBtn.addEventListener("click", () => {
      stopFn();
      setState(false);
    });
    new MutationObserver(() => {
      titleEl.textContent = currentDisplayEl.textContent;
    }).observe(currentDisplayEl, {
      childList: true,
      characterData: true,
      subtree: true
    });
    makeDraggable(mini, handle);
    registerMiniPlayer(key, () => setState(false), () => isOn);
    return {
      onPageEnter() {
        if (isOn) setState(false);
      }
    };
  }
  const minis = {
    documentary: setupVideoFamilyMini({
      key: "documentary",
      playerEl: documentaryPlayer,
      dockEl: document.getElementById("documentary-dock"),
      currentIdGetter: () => currentDocumentaryId,
      currentDisplayEl: currentDocumentaryDisplay,
      playPauseBtn: playPauseDocumentaryBtn,
      prevBtn: prevDocumentaryBtn,
      nextBtn: nextDocumentaryBtn,
      sourceLabel: "Documentary Terminal",
      pageKey: "documentary"
    }),
    movie: setupVideoFamilyMini({
      key: "movie",
      playerEl: moviePlayer,
      dockEl: document.getElementById("movie-dock"),
      currentIdGetter: () => currentMovieId,
      currentDisplayEl: currentMovieDisplay,
      playPauseBtn: playPauseMovieBtn,
      prevBtn: prevMovieBtn,
      nextBtn: nextMovieBtn,
      sourceLabel: "Movie Terminal",
      pageKey: "movie"
    }),
    comedy: setupVideoFamilyMini({
      key: "comedy",
      playerEl: comedyPlayer,
      dockEl: document.getElementById("comedy-dock"),
      currentIdGetter: () => currentComedyId,
      currentDisplayEl: currentComedyDisplay,
      playPauseBtn: playPauseComedyBtn,
      prevBtn: prevComedyBtn,
      nextBtn: nextComedyBtn,
      sourceLabel: "Comedy Terminal",
      pageKey: "comedy"
    }),
    webseries: setupVideoFamilyMini({
      key: "webseries",
      playerEl: webseriesPlayer,
      dockEl: document.getElementById("webseries-dock"),
      currentIdGetter: () => currentWebSeriesId,
      currentDisplayEl: currentWebSeriesDisplay,
      playPauseBtn: playPauseWebSeriesBtn,
      prevBtn: prevWebSeriesBtn,
      nextBtn: nextWebSeriesBtn,
      sourceLabel: "Web Series Terminal",
      pageKey: "webseries"
    }),
    games: setupSimpleMini({
      key: "games",
      currentIdGetter: () => currentGameId,
      currentDisplayEl: currentGameDisplay,
      stopFn: stopGame,
      pageKey: "games"
    }),
    books: setupSimpleMini({
      key: "books",
      currentIdGetter: () => currentBookId,
      currentDisplayEl: currentBookDisplay,
      stopFn: closeBook,
      pageKey: "books"
    }),
    gamevideo: setupVideoFamilyMini({
      key: "gamevideo",
      playerEl: gamevideoPlayer,
      dockEl: document.getElementById("gamevideo-dock"),
      currentIdGetter: () => currentGameVideoId,
      currentDisplayEl: currentGameVideoDisplay,
      playPauseBtn: playPauseGameVideoBtn,
      prevBtn: prevGameVideoBtn,
      nextBtn: nextGameVideoBtn,
      sourceLabel: "Game Video Terminal",
      pageKey: "gamevideo"
    }),
    gamemovie: setupVideoFamilyMini({
      key: "gamemovie",
      playerEl: gamemoviePlayer,
      dockEl: document.getElementById("gamemovie-dock"),
      currentIdGetter: () => currentGameMovieId,
      currentDisplayEl: currentGameMovieDisplay,
      playPauseBtn: playPauseGameMovieBtn,
      prevBtn: prevGameMovieBtn,
      nextBtn: nextGameMovieBtn,
      sourceLabel: "Game Movie Terminal",
      pageKey: "gamemovie"
    }),
    bookvideo: setupVideoFamilyMini({
      key: "bookvideo",
      playerEl: bookvideoPlayer,
      dockEl: document.getElementById("bookvideo-dock"),
      currentIdGetter: () => currentBookVideoId,
      currentDisplayEl: currentBookVideoDisplay,
      playPauseBtn: playPauseBookVideoBtn,
      prevBtn: prevBookVideoBtn,
      nextBtn: nextBookVideoBtn,
      sourceLabel: "Book Video Terminal",
      pageKey: "bookvideo"
    }),
    bookmovie: setupVideoFamilyMini({
      key: "bookmovie",
      playerEl: bookmoviePlayer,
      dockEl: document.getElementById("bookmovie-dock"),
      currentIdGetter: () => currentBookMovieId,
      currentDisplayEl: currentBookMovieDisplay,
      playPauseBtn: playPauseBookMovieBtn,
      prevBtn: prevBookMovieBtn,
      nextBtn: nextBookMovieBtn,
      sourceLabel: "Book Movie Terminal",
      pageKey: "bookmovie"
    }),
    presentations: setupSimpleMini({
      key: "presentations",
      currentIdGetter: () => currentPresentationId,
      currentDisplayEl: currentPresentationDisplay,
      stopFn: closePresentation,
      pageKey: "presentations"
    })
  };
  const prevOnPageChange = onPageChange;
  onPageChange = name => {
    if (prevOnPageChange) prevOnPageChange(name);
    const m = minis[name];
    if (m) m.onPageEnter();
  };
})();

window.addEventListener("beforeunload", () => {
  if (audioPlayer.dataset.url) URL.revokeObjectURL(audioPlayer.dataset.url);
  if (videoPlayer.dataset.url) URL.revokeObjectURL(videoPlayer.dataset.url);
  if (podcastPlayer.dataset.url) URL.revokeObjectURL(podcastPlayer.dataset.url);
  if (gameFrame.dataset.url) URL.revokeObjectURL(gameFrame.dataset.url);
  if (bookFrame.dataset.url) URL.revokeObjectURL(bookFrame.dataset.url);
  if (gamevideoPlayer.dataset.url) URL.revokeObjectURL(gamevideoPlayer.dataset.url);
  if (gamemoviePlayer.dataset.url) URL.revokeObjectURL(gamemoviePlayer.dataset.url);
  if (bookvideoPlayer.dataset.url) URL.revokeObjectURL(bookvideoPlayer.dataset.url);
  if (bookmoviePlayer.dataset.url) URL.revokeObjectURL(bookmoviePlayer.dataset.url);
  if (presentationFrame.dataset.url) URL.revokeObjectURL(presentationFrame.dataset.url);
});

window.addEventListener("load", () => {
  setupBannerHandling();
  loadNovaConfig().finally(() => initAppData());
});

const QUEUE_TYPES = {
  music: {
    getLibrary: () => music,
    getName: item => item.name,
    playFn: id => {
      playlistPlaying = false;
      currentPlaylist = null;
      playMusicById(id);
    },
    listId: "music-queue-list",
    countId: "music-queue-count",
    sourceListId: "music-list"
  },
  video: {
    getLibrary: () => videos,
    getName: item => item.name,
    playFn: id => {
      videoPlaylistPlaying = false;
      currentVideoPlaylist = null;
      playVideoById(id);
    },
    listId: "video-queue-list",
    countId: "video-queue-count",
    sourceListId: "video-list"
  },
  documentary: {
    getLibrary: () => documentary,
    getName: item => item.name,
    playFn: id => playDocumentaryById(id),
    listId: "documentary-queue-list",
    countId: "documentary-queue-count",
    sourceListId: "documentary-list"
  },
  movie: {
    getLibrary: () => movie,
    getName: item => item.name,
    playFn: id => playMovieById(id),
    listId: "movie-queue-list",
    countId: "movie-queue-count",
    sourceListId: "movie-list"
  },
  comedy: {
    getLibrary: () => comedy,
    getName: item => item.name,
    playFn: id => playComedyById(id),
    listId: "comedy-queue-list",
    countId: "comedy-queue-count",
    sourceListId: "comedy-list"
  },
  webseries: {
    getLibrary: () => webseries,
    getName: item => item.name,
    playFn: id => playWebSeriesById(id),
    listId: "webseries-queue-list",
    countId: "webseries-queue-count",
    sourceListId: "webseries-list"
  },
  podcast: {
    getLibrary: () => podcasts,
    getName: item => item.name,
    playFn: id => {
      podcastPlaylistPlaying = false;
      currentPodcastPlaylist = null;
      playPodcastById(id);
    },
    listId: "podcast-queue-list",
    countId: "podcast-queue-count",
    sourceListId: "podcast-list"
  },
  gamevideo: {
    getLibrary: () => gamevideo,
    getName: item => item.name,
    playFn: id => playGameVideoById(id),
    listId: "gamevideo-queue-list",
    countId: "gamevideo-queue-count",
    sourceListId: "gamevideo-list"
  },
  gamemovie: {
    getLibrary: () => gamemovie,
    getName: item => item.name,
    playFn: id => playGameMovieById(id),
    listId: "gamemovie-queue-list",
    countId: "gamemovie-queue-count",
    sourceListId: "gamemovie-list"
  },
  bookvideo: {
    getLibrary: () => bookvideo,
    getName: item => item.name,
    playFn: id => playBookVideoById(id),
    listId: "bookvideo-queue-list",
    countId: "bookvideo-queue-count",
    sourceListId: "bookvideo-list"
  },
  bookmovie: {
    getLibrary: () => bookmovie,
    getName: item => item.name,
    playFn: id => playBookMovieById(id),
    listId: "bookmovie-queue-list",
    countId: "bookmovie-queue-count",
    sourceListId: "bookmovie-list"
  }
};

let mediaQueues = {
  music: [],
  video: [],
  documentary: [],
  movie: [],
  comedy: [],
  webseries: [],
  podcast: [],
  gamevideo: [],
  gamemovie: [],
  bookvideo: [],
  bookmovie: []
};

let queueRepeat = {
  music: false,
  video: false,
  documentary: false,
  movie: false,
  comedy: false,
  webseries: false,
  podcast: false,
  gamevideo: false,
  gamemovie: false,
  bookvideo: false,
  bookmovie: false
};

function saveQueue(type) {
  appSet(`${type}Queue`, mediaQueues[type]);
}

function loadQueue(type) {
  mediaQueues[type] = appGet(`${type}Queue`, []);
}

function saveQueueRepeat(type) {
  appSet(`${type}QueueRepeat`, queueRepeat[type]);
}

function loadQueueRepeat(type) {
  queueRepeat[type] = appGet(`${type}QueueRepeat`, false);
}

function setQueueRepeatButtonLabel(type) {
  const btn = document.getElementById(`btn-repeat-${type}-queue`);
  if (!btn) return;
  btn.textContent = `🔁 Repeat Queue: ${queueRepeat[type] ? "On" : "Off"}`;
  btn.classList.toggle("active", !!queueRepeat[type]);
}

function toggleQueueRepeat(type) {
  queueRepeat[type] = !queueRepeat[type];
  saveQueueRepeat(type);
  setQueueRepeatButtonLabel(type);
}

function addToQueue(type, id) {
  mediaQueues[type].push(id);
  saveQueue(type);
  renderQueue(type);
}

function addAllToQueue(type) {
  QUEUE_TYPES[type].getLibrary().forEach(item => mediaQueues[type].push(item.id));
  saveQueue(type);
  renderQueue(type);
}

function addSelectedToQueue(type) {
  const sourceListId = QUEUE_TYPES[type].sourceListId;
  const checked = document.querySelectorAll(`#${sourceListId} input[type="checkbox"]:checked`);
  if (!checked.length) return alert("No items selected");
  checked.forEach(cb => {
    const id = Number(cb.dataset.id);
    if (!Number.isNaN(id)) mediaQueues[type].push(id);
  });
  saveQueue(type);
  renderQueue(type);
}

function removeFromQueueAt(type, index) {
  mediaQueues[type].splice(index, 1);
  saveQueue(type);
  renderQueue(type);
}

function clearQueue(type) {
  mediaQueues[type] = [];
  saveQueue(type);
  renderQueue(type);
}

function reorderQueue(type, newOrderIds) {
  mediaQueues[type] = newOrderIds.filter(id => !Number.isNaN(id));
  saveQueue(type);
}

function moveQueueItem(type, index, delta) {
  const arr = mediaQueues[type];
  if (!arr) return;
  const newIndex = index + delta;
  if (newIndex < 0 || newIndex >= arr.length) return;
  const [moved] = arr.splice(index, 1);
  arr.splice(newIndex, 0, moved);
  saveQueue(type);
  renderQueue(type);
}

function consumeQueueNext(type) {
  if (!mediaQueues[type] || !mediaQueues[type].length) return null;
  const id = mediaQueues[type].shift();
  if (queueRepeat[type]) mediaQueues[type].push(id);
  saveQueue(type);
  renderQueue(type);
  return id;
}

function playQueueNow(type) {
  const id = consumeQueueNext(type);
  if (id === null) return;
  QUEUE_TYPES[type].playFn(id);
}

function renderQueue(type) {
  const cfg = QUEUE_TYPES[type];
  const listEl = document.getElementById(cfg.listId);
  if (!listEl) return;
  const countEl = document.getElementById(cfg.countId);
  const library = cfg.getLibrary();
  const queue = mediaQueues[type] || [];
  listEl.innerHTML = "";
  if (!queue.length) {
    const empty = document.createElement("li");
    empty.className = "queue-empty-row";
    empty.textContent = "Queue is empty";
    listEl.appendChild(empty);
  } else {
    queue.forEach((id, index) => {
      const item = library.find(m => m.id === id);
      const li = document.createElement("li");
      li.className = "queue-row";
      li.dataset.id = id;
      const handle = document.createElement("span");
      handle.className = "queue-drag-handle";
      handle.textContent = "⋮⋮";
      handle.title = "Drag to reorder";
      handle.setAttribute("aria-hidden", "true");
      const posBadge = document.createElement("span");
      posBadge.className = "queue-position";
      posBadge.textContent = `${index + 1}.`;
      const name = document.createElement("span");
      name.textContent = item ? cfg.getName(item) : "(removed item)";
      const upBtn = document.createElement("button");
      upBtn.className = "queue-move-btn";
      upBtn.textContent = "▲";
      upBtn.title = "Move up";
      upBtn.setAttribute("aria-label", "Move up in queue");
      upBtn.disabled = index === 0;
      upBtn.addEventListener("click", () => moveQueueItem(type, index, -1));
      const downBtn = document.createElement("button");
      downBtn.className = "queue-move-btn";
      downBtn.textContent = "▼";
      downBtn.title = "Move down";
      downBtn.setAttribute("aria-label", "Move down in queue");
      downBtn.disabled = index === queue.length - 1;
      downBtn.addEventListener("click", () => moveQueueItem(type, index, 1));
      const playBtn = document.createElement("button");
      playBtn.textContent = "▶";
      playBtn.className = "media-row-play-btn";
      playBtn.title = "Play now";
      playBtn.addEventListener("click", () => {
        mediaQueues[type].splice(index, 1);
        saveQueue(type);
        renderQueue(type);
        if (item) cfg.playFn(id);
      });
      const removeBtn = document.createElement("button");
      removeBtn.textContent = "✕";
      removeBtn.title = "Remove from queue";
      removeBtn.addEventListener("click", () => removeFromQueueAt(type, index));
      li.append(handle, posBadge, name, upBtn, downBtn, playBtn, removeBtn);
      listEl.appendChild(li);
    });
  }
  if (countEl) countEl.textContent = `${queue.length} queued`;
}

Object.keys(QUEUE_TYPES).forEach(type => {
  const cfg = QUEUE_TYPES[type];
  const addSelectedBtn = document.getElementById(`btn-add-selected-to-${type}-queue`);
  if (addSelectedBtn) addSelectedBtn.addEventListener("click", () => addSelectedToQueue(type));
  const addAllBtn = document.getElementById(`btn-add-all-to-${type}-queue`);
  if (addAllBtn) addAllBtn.addEventListener("click", () => addAllToQueue(type));
  const clearBtn = document.getElementById(`btn-clear-${type}-queue`);
  if (clearBtn) clearBtn.addEventListener("click", () => clearQueue(type));
  const playBtn = document.getElementById(`btn-play-${type}-queue`);
  if (playBtn) playBtn.addEventListener("click", () => playQueueNow(type));
  const repeatBtn = document.getElementById(`btn-repeat-${type}-queue`);
  if (repeatBtn) repeatBtn.addEventListener("click", () => toggleQueueRepeat(type));
  loadQueueRepeat(type);
  setQueueRepeatButtonLabel(type);
  const listEl = document.getElementById(cfg.listId);
  if (listEl) enableDragReorder(listEl, newOrder => reorderQueue(type, newOrder));
  renderQueue(type);
});

(function() {
  const NS_HISTORY_TERMINALS = {
    documentary: {
      icon: "🎥",
      recentEmpty: "No recent uploads in Documentary Terminal.",
      historyEmpty: "No plays in Documentary Terminal.",
      playFnName: "playDocumentaryById",
      displaySource: "Documentary Terminal"
    },
    movie: {
      icon: "🍿",
      recentEmpty: "No recent uploads in Movie Terminal.",
      historyEmpty: "No plays in Movie Terminal.",
      playFnName: "playMovieById",
      displaySource: "Movie Terminal"
    },
    comedy: {
      icon: "🎤",
      recentEmpty: "No recent uploads in Comedy Terminal.",
      historyEmpty: "No plays in Comedy Terminal.",
      playFnName: "playComedyById",
      displaySource: "Comedy Terminal"
    },
    webseries: {
      icon: "📺",
      recentEmpty: "No recent uploads in Web Series Terminal.",
      historyEmpty: "No plays in Web Series Terminal.",
      playFnName: "playWebSeriesById",
      displaySource: "Web Series Terminal"
    },
    games: {
      icon: "🎮",
      recentEmpty: "No recent uploads in Game Terminal.",
      historyEmpty: "No plays in Game Terminal.",
      playFnName: "playGameById",
      displaySource: "Game Terminal"
    },
    books: {
      icon: "📚",
      recentEmpty: "No recent uploads in Book Terminal.",
      historyEmpty: "No plays in Book Terminal.",
      playFnName: "viewBookById",
      displaySource: "Book Terminal"
    },
    gamevideo: {
      icon: "🎞️",
      recentEmpty: "No recent uploads in Game Video Terminal.",
      historyEmpty: "No plays in Game Video Terminal.",
      playFnName: "playGameVideoById",
      displaySource: "Game Video Terminal"
    },
    gamemovie: {
      icon: "🕹️",
      recentEmpty: "No recent uploads in Game Movie Terminal.",
      historyEmpty: "No plays in Game Movie Terminal.",
      playFnName: "playGameMovieById",
      displaySource: "Game Movie Terminal"
    },
    bookvideo: {
      icon: "📼",
      recentEmpty: "No recent uploads in Book Video Terminal.",
      historyEmpty: "No plays in Book Video Terminal.",
      playFnName: "playBookVideoById",
      displaySource: "Book Video Terminal"
    },
    bookmovie: {
      icon: "🎟️",
      recentEmpty: "No recent uploads in Book Movie Terminal.",
      historyEmpty: "No plays in Book Movie Terminal.",
      playFnName: "playBookMovieById",
      displaySource: "Book Movie Terminal"
    },
    presentations: {
      icon: "📽️",
      recentEmpty: "No recent uploads in Presentations Terminal.",
      historyEmpty: "No plays in Presentations Terminal.",
      playFnName: "viewPresentationById",
      displaySource: "Presentations Terminal"
    }
  };
  Object.assign(HISTORY_TYPE_ICONS, {
    documentary: "🎥",
    movie: "🍿",
    comedy: "🎤",
    webseries: "📺",
    games: "🎮",
    books: "📚",
    gamevideo: "🎞️",
    gamemovie: "🕹️",
    bookvideo: "📼",
    bookmovie: "🎟️",
    presentations: "📽️"
  });
  function renderNsRecentEmpty(type) {
    const el = document.getElementById(`${type}-recent-list`);
    if (!el) return;
    el.innerHTML = "";
    el.appendChild(buildHistoryRow({
      empty: true,
      title: NS_HISTORY_TERMINALS[type].recentEmpty,
      removeClass: "recent-remove-btn"
    }));
  }
  function renderNsHistory(type) {
    const el = document.getElementById(`${type}-history-list`);
    renderHistoryList(el, type);
  }
  function renderNsHistoryEmptyFallback(type) {
    const el = document.getElementById(`${type}-history-list`);
    if (!el) return;
    el.innerHTML = "";
    el.appendChild(buildHistoryRow({
      empty: true,
      title: NS_HISTORY_TERMINALS[type].historyEmpty,
      removeClass: "history-remove-btn"
    }));
  }
  function wirePlayTracking(type, itemLookup) {
    const cfg = NS_HISTORY_TERMINALS[type];
    const original = window[cfg.playFnName];
    if (typeof original !== "function" || original.__nsWrapped) return;
    const wrapped = function(id, ...rest) {
      const result = original.call(this, id, ...rest);
      const item = itemLookup(id);
      if (item) recordPlay(type, item.name, cfg.displaySource);
      return result;
    };
    wrapped.__nsWrapped = true;
    window[cfg.playFnName] = wrapped;
  }
  function wireClearButtons(type) {
    const clearRecentBtn = document.getElementById(`btn-clear-${type}-recent`);
    if (clearRecentBtn && !clearRecentBtn.__nsWired) {
      clearRecentBtn.__nsWired = true;
      clearRecentBtn.addEventListener("click", () => renderNsRecentEmpty(type));
    }
    const clearHistoryBtn = document.getElementById(`btn-clear-${type}-history`);
    if (clearHistoryBtn && !clearHistoryBtn.__nsWired) {
      clearHistoryBtn.__nsWired = true;
      clearHistoryBtn.addEventListener("click", () => {
        if (!historyReady) return;
        historyData.play_log = historyData.play_log.filter(row => row.media_type !== type);
        saveHistoryBuffer();
        refreshHistoryCache();
        renderNsHistory(type);
      });
    }
    const downloadRecentBtn = document.getElementById(`btn-download-${type}-recent`);
    if (downloadRecentBtn && !downloadRecentBtn.__nsWired) {
      downloadRecentBtn.__nsWired = true;
      downloadRecentBtn.addEventListener("click", () => {
        alert("Nothing to download yet — items you add will appear here.");
      });
    }
  }
  function initPrismActivityTracking() {
    wirePlayTracking("documentary", id => typeof documentary !== "undefined" ? documentary.find(v => v.id === id) : null);
    wirePlayTracking("movie", id => typeof movie !== "undefined" ? movie.find(v => v.id === id) : null);
    wirePlayTracking("comedy", id => typeof comedy !== "undefined" ? comedy.find(v => v.id === id) : null);
    wirePlayTracking("webseries", id => typeof webseries !== "undefined" ? webseries.find(v => v.id === id) : null);
    wirePlayTracking("games", id => typeof games !== "undefined" ? games.find(v => v.id === id) : null);
    wirePlayTracking("books", id => typeof books !== "undefined" ? books.find(v => v.id === id) : null);
    wirePlayTracking("gamevideo", id => typeof gamevideo !== "undefined" ? gamevideo.find(v => v.id === id) : null);
    wirePlayTracking("gamemovie", id => typeof gamemovie !== "undefined" ? gamemovie.find(v => v.id === id) : null);
    wirePlayTracking("bookvideo", id => typeof bookvideo !== "undefined" ? bookvideo.find(v => v.id === id) : null);
    wirePlayTracking("bookmovie", id => typeof bookmovie !== "undefined" ? bookmovie.find(v => v.id === id) : null);
    wirePlayTracking("presentations", id => typeof presentations !== "undefined" ? presentations.find(v => v.id === id) : null);
    Object.keys(NS_HISTORY_TERMINALS).forEach(type => {
      renderNsRecentEmpty(type);
      if (typeof historyReady !== "undefined" && historyReady) {
        renderNsHistory(type);
      } else {
        renderNsHistoryEmptyFallback(type);
      }
      wireClearButtons(type);
    });
  }
  const nsHistoryPoll = setInterval(() => {
    if (typeof historyReady !== "undefined" && historyReady) {
      Object.keys(NS_HISTORY_TERMINALS).forEach(renderNsHistory);
      clearInterval(nsHistoryPoll);
    }
  }, 400);
  setTimeout(() => clearInterval(nsHistoryPoll), 8e3);
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", initPrismActivityTracking);
  } else {
    initPrismActivityTracking();
  }
})();

(function() {
  var yearEl = document.getElementById("footer-year");
  if (yearEl) yearEl.textContent = "© " + (new Date).getFullYear();
})();

function assignFilesToInputAndDispatch(targetInput, files) {
  const dt = new DataTransfer;
  files.forEach(f => dt.items.add(f));
  targetInput.files = dt.files;
  targetInput.dispatchEvent(new Event("change"));
}

const FOLDER_UPLOAD_WIRING = [ {
  folderInputId: "music-upload-folder",
  targetInputId: "music-upload",
  mediaType: "audio"
}, {
  folderInputId: "podcast-upload-folder",
  targetInputId: "podcast-upload",
  mediaType: "audio"
}, {
  folderInputId: "video-upload-folder",
  targetInputId: "video-upload",
  mediaType: "video"
}, {
  folderInputId: "documentary-upload-folder",
  targetInputId: "documentary-upload",
  mediaType: "video"
}, {
  folderInputId: "movie-upload-folder",
  targetInputId: "movie-upload",
  mediaType: "video"
}, {
  folderInputId: "comedy-upload-folder",
  targetInputId: "comedy-upload",
  mediaType: "video"
}, {
  folderInputId: "webseries-upload-folder",
  targetInputId: "webseries-upload",
  mediaType: "video"
}, {
  folderInputId: "games-upload-folder",
  targetInputId: "games-upload",
  mediaType: "game"
}, {
  folderInputId: "books-upload-folder",
  targetInputId: "books-upload",
  mediaType: "pdf"
}, {
  folderInputId: "gamevideo-upload-folder",
  targetInputId: "gamevideo-upload",
  mediaType: "video"
}, {
  folderInputId: "gamemovie-upload-folder",
  targetInputId: "gamemovie-upload",
  mediaType: "video"
}, {
  folderInputId: "bookvideo-upload-folder",
  targetInputId: "bookvideo-upload",
  mediaType: "video"
}, {
  folderInputId: "bookmovie-upload-folder",
  targetInputId: "bookmovie-upload",
  mediaType: "video"
}, {
  folderInputId: "presentations-upload-folder",
  targetInputId: "presentations-upload",
  mediaType: "presentation"
} ];

FOLDER_UPLOAD_WIRING.forEach(cfg => {
  const folderInput = document.getElementById(cfg.folderInputId);
  const targetInput = document.getElementById(cfg.targetInputId);
  if (!folderInput || !targetInput) return;
  folderInput.addEventListener("change", () => {
    const rawFiles = [ ...folderInput.files ];
    folderInput.value = "";
    if (!rawFiles.length) return;
    const files = filterUploadedMediaFiles(rawFiles, cfg.mediaType);
    if (!files.length) {
      const allowedExt = ZIP_EXTENSIONS_BY_TYPE[cfg.mediaType] || [];
      alert(`That folder doesn't contain any files matching the types this terminal supports${allowedExt.length ? ` (${allowedExt.join(", ")})` : ""}.`);
      return;
    }
    assignFilesToInputAndDispatch(targetInput, files);
  });
});

const FOLDER_PLAYLIST_IMPORT_WIRING = [ {
  folderInputId: "playlist-import-folder",
  targetInputId: "playlist-import"
}, {
  folderInputId: "podcast-playlist-import-folder",
  targetInputId: "podcast-playlist-import"
}, {
  folderInputId: "video-playlist-import-folder",
  targetInputId: "video-playlist-import"
}, {
  folderInputId: "documentary-playlist-import-folder",
  targetInputId: "documentary-playlist-import"
}, {
  folderInputId: "movie-playlist-import-folder",
  targetInputId: "movie-playlist-import"
}, {
  folderInputId: "comedy-playlist-import-folder",
  targetInputId: "comedy-playlist-import"
}, {
  folderInputId: "webseries-playlist-import-folder",
  targetInputId: "webseries-playlist-import"
}, {
  folderInputId: "games-playlist-import-folder",
  targetInputId: "games-playlist-import"
}, {
  folderInputId: "books-playlist-import-folder",
  targetInputId: "books-playlist-import"
}, {
  folderInputId: "gamevideo-playlist-import-folder",
  targetInputId: "gamevideo-playlist-import"
}, {
  folderInputId: "gamemovie-playlist-import-folder",
  targetInputId: "gamemovie-playlist-import"
}, {
  folderInputId: "bookvideo-playlist-import-folder",
  targetInputId: "bookvideo-playlist-import"
}, {
  folderInputId: "bookmovie-playlist-import-folder",
  targetInputId: "bookmovie-playlist-import"
}, {
  folderInputId: "presentations-playlist-import-folder",
  targetInputId: "presentations-playlist-import"
} ];

function folderNameFromFiles(files) {
  const relPath = files[0] && files[0].webkitRelativePath || "";
  return (relPath.split("/")[0] || "Imported Playlist").trim() || "Imported Playlist";
}

FOLDER_PLAYLIST_IMPORT_WIRING.forEach(cfg => {
  const folderInput = document.getElementById(cfg.folderInputId);
  if (!folderInput) return;
  folderInput.addEventListener("change", async () => {
    const rawFiles = [ ...folderInput.files ];
    folderInput.value = "";
    if (!rawFiles.length) return;
    const handler = PLAYLIST_FOLDER_IMPORT_HANDLERS[cfg.targetInputId];
    if (!handler) return;
    await handler(rawFiles, folderNameFromFiles(rawFiles));
  });
});

function readDirectoryEntries(dirReader) {
  return new Promise((resolve, reject) => {
    const all = [];
    function readBatch() {
      dirReader.readEntries(entries => {
        if (!entries.length) return resolve(all);
        all.push(...entries);
        readBatch();
      }, reject);
    }
    readBatch();
  });
}

function fileFromEntry(entry) {
  return new Promise((resolve, reject) => entry.file(resolve, reject));
}

function setWebkitRelativePath(file, relPath) {
  try {
    Object.defineProperty(file, "webkitRelativePath", {
      value: relPath,
      configurable: true
    });
  } catch (err) {
    try {
      file.webkitRelativePath = relPath;
    } catch (err2) {}
  }
}

async function walkEntry(entry, basePath, out) {
  if (entry.isFile) {
    const file = await fileFromEntry(entry);
    const relPath = basePath ? `${basePath}/${entry.name}` : entry.name;
    if (basePath) setWebkitRelativePath(file, relPath);
    out.push(file);
  } else if (entry.isDirectory) {
    const reader = entry.createReader();
    const entries = await readDirectoryEntries(reader);
    const nextBase = basePath ? `${basePath}/${entry.name}` : entry.name;
    for (const child of entries) {
      await walkEntry(child, nextBase, out);
    }
  }
}

async function collectDroppedFiles(dataTransfer) {
  const items = dataTransfer.items;
  if (items && items.length && typeof items[0].webkitGetAsEntry === "function") {
    const out = [];
    const entries = [];
    for (let i = 0; i < items.length; i++) {
      const item = items[i];
      if (item.kind !== "file") continue;
      const entry = item.webkitGetAsEntry();
      if (entry) {
        entries.push(entry);
      } else {
        const file = item.getAsFile();
        if (file) out.push(file);
      }
    }
    for (const entry of entries) {
      await walkEntry(entry, "", out);
    }
    return out;
  }
  return [ ...dataTransfer.files || [] ];
}

function wireUploadDropZone(container, targetInput, mediaType) {
  if (!container || !targetInput) return;
  container.classList.add("upload-drop-target");
  container.addEventListener("dragover", e => {
    if (!e.dataTransfer.types.includes("Files")) return;
    e.preventDefault();
    e.dataTransfer.dropEffect = "copy";
    container.classList.add("drag-over");
  });
  container.addEventListener("dragleave", e => {
    if (!container.contains(e.relatedTarget)) container.classList.remove("drag-over");
  });
  container.addEventListener("drop", async e => {
    if (!e.dataTransfer.types.includes("Files")) return;
    e.preventDefault();
    container.classList.remove("drag-over");
    const rawFiles = await collectDroppedFiles(e.dataTransfer);
    if (!rawFiles.length) return;
    const files = filterUploadedMediaFiles(rawFiles, mediaType);
    if (!files.length) {
      const allowedExt = ZIP_EXTENSIONS_BY_TYPE[mediaType] || [];
      alert(`That doesn't contain any files matching the types this terminal supports${allowedExt.length ? ` (${allowedExt.join(", ")})` : ""}.`);
      return;
    }
    assignFilesToInputAndDispatch(targetInput, files);
  });
}

function wirePlaylistImportDropZone(container, handler) {
  if (!container || !handler) return;
  container.classList.add("upload-drop-target");
  container.addEventListener("dragover", e => {
    if (!e.dataTransfer.types.includes("Files")) return;
    e.preventDefault();
    e.dataTransfer.dropEffect = "copy";
    container.classList.add("drag-over");
  });
  container.addEventListener("dragleave", e => {
    if (!container.contains(e.relatedTarget)) container.classList.remove("drag-over");
  });
  container.addEventListener("drop", async e => {
    if (!e.dataTransfer.types.includes("Files")) return;
    e.preventDefault();
    container.classList.remove("drag-over");
    const rawFiles = await collectDroppedFiles(e.dataTransfer);
    if (!rawFiles.length) return;
    await handler(rawFiles, folderNameFromFiles(rawFiles));
  });
}

FOLDER_UPLOAD_WIRING.forEach(cfg => {
  const targetInput = document.getElementById(cfg.targetInputId);
  if (!targetInput) return;
  wireUploadDropZone(targetInput.closest(".column"), targetInput, cfg.mediaType);
});

FOLDER_PLAYLIST_IMPORT_WIRING.forEach(cfg => {
  const targetInput = document.getElementById(cfg.targetInputId);
  if (!targetInput) return;
  const handler = PLAYLIST_FOLDER_IMPORT_HANDLERS[cfg.targetInputId];
  if (!handler) return;
  wirePlaylistImportDropZone(targetInput.closest(".column"), handler);
});