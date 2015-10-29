"use strict";
// This object will hold all exports.
var Haste = {};

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof F) {
            f = E(B(f));
        }
        if(f instanceof PAP) {
            // f is a partial application
            if(args.length == f.arity) {
                // Saturated application
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                // Application is still unsaturated
                return new PAP(f.f, f.args.concat(args));
            } else {
                // Application is oversaturated; 
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else if(f instanceof Function) {
            if(args.length == f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        return t.x;
    } else {
        return t;
    }
}

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        f = fun();
    }
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return [0, (a-a%b)/b, a%b];
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return [0, x & 0xffffffff, x > 0x7fffffff];
}

function subC(a, b) {
    var x = a-b;
    return [0, x & 0xffffffff, x < -2147483648];
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, [0]);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return [1,str.charCodeAt(i),new T(function() {
            return unAppCStr(str,chrs,i+1);
        })];
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str[0] == 1; str = E(str[2])) {
        s += String.fromCharCode(E(str[1]));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x[1];
    return x[2];
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Array) {
        return x[0];
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(I_getBits(i,0)) + popCnt(I_getBits(i,1));
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return [0,1,0,0,0];
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return [0, sign*man, exp];
}

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return [0,1,0,0,0];
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return [0, sign, manHigh, manLow, exp];
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs[0]) {
        strs = E(strs);
        arr.push(E(strs[1]));
        strs = E(strs[2]);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return [0];
    }
    return [1,hs];
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return [0, jsRead(obj)];
    case 'string':
        return [1, obj];
    case 'boolean':
        return [2, obj]; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return [3, arr2lst_json(obj, 0)];
        } else if (obj == null) {
            return [5];
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = [1, [0, ks[i], toHS(obj[ks[i]])], xs];
            }
            return [4, xs];
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return [0];
    }
    return [1, toHS(arr[elem]), new T(function() {return arr2lst_json(arr,elem+1);}),true]
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return [0, 0, undefined];
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return [0, 1, val];
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

var Integer = function(bits, sign) {
  this.bits_ = [];
  this.sign_ = sign;

  var top = true;
  for (var i = bits.length - 1; i >= 0; i--) {
    var val = bits[i] | 0;
    if (!top || val != sign) {
      this.bits_[i] = val;
      top = false;
    }
  }
};

Integer.IntCache_ = {};

var I_fromInt = function(value) {
  if (-128 <= value && value < 128) {
    var cachedObj = Integer.IntCache_[value];
    if (cachedObj) {
      return cachedObj;
    }
  }

  var obj = new Integer([value | 0], value < 0 ? -1 : 0);
  if (-128 <= value && value < 128) {
    Integer.IntCache_[value] = obj;
  }
  return obj;
};

var I_fromNumber = function(value) {
  if (isNaN(value) || !isFinite(value)) {
    return Integer.ZERO;
  } else if (value < 0) {
    return I_negate(I_fromNumber(-value));
  } else {
    var bits = [];
    var pow = 1;
    for (var i = 0; value >= pow; i++) {
      bits[i] = (value / pow) | 0;
      pow *= Integer.TWO_PWR_32_DBL_;
    }
    return new Integer(bits, 0);
  }
};

var I_fromBits = function(bits) {
  var high = bits[bits.length - 1];
  return new Integer(bits, high & (1 << 31) ? -1 : 0);
};

var I_fromString = function(str, opt_radix) {
  if (str.length == 0) {
    throw Error('number format error: empty string');
  }

  var radix = opt_radix || 10;
  if (radix < 2 || 36 < radix) {
    throw Error('radix out of range: ' + radix);
  }

  if (str.charAt(0) == '-') {
    return I_negate(I_fromString(str.substring(1), radix));
  } else if (str.indexOf('-') >= 0) {
    throw Error('number format error: interior "-" character');
  }

  var radixToPower = I_fromNumber(Math.pow(radix, 8));

  var result = Integer.ZERO;
  for (var i = 0; i < str.length; i += 8) {
    var size = Math.min(8, str.length - i);
    var value = parseInt(str.substring(i, i + size), radix);
    if (size < 8) {
      var power = I_fromNumber(Math.pow(radix, size));
      result = I_add(I_mul(result, power), I_fromNumber(value));
    } else {
      result = I_mul(result, radixToPower);
      result = I_add(result, I_fromNumber(value));
    }
  }
  return result;
};


Integer.TWO_PWR_32_DBL_ = (1 << 16) * (1 << 16);
Integer.ZERO = I_fromInt(0);
Integer.ONE = I_fromInt(1);
Integer.TWO_PWR_24_ = I_fromInt(1 << 24);

var I_toInt = function(self) {
  return self.bits_.length > 0 ? self.bits_[0] : self.sign_;
};

var I_toWord = function(self) {
  return I_toInt(self) >>> 0;
};

var I_toNumber = function(self) {
  if (isNegative(self)) {
    return -I_toNumber(I_negate(self));
  } else {
    var val = 0;
    var pow = 1;
    for (var i = 0; i < self.bits_.length; i++) {
      val += I_getBitsUnsigned(self, i) * pow;
      pow *= Integer.TWO_PWR_32_DBL_;
    }
    return val;
  }
};

var I_getBits = function(self, index) {
  if (index < 0) {
    return 0;
  } else if (index < self.bits_.length) {
    return self.bits_[index];
  } else {
    return self.sign_;
  }
};

var I_getBitsUnsigned = function(self, index) {
  var val = I_getBits(self, index);
  return val >= 0 ? val : Integer.TWO_PWR_32_DBL_ + val;
};

var getSign = function(self) {
  return self.sign_;
};

var isZero = function(self) {
  if (self.sign_ != 0) {
    return false;
  }
  for (var i = 0; i < self.bits_.length; i++) {
    if (self.bits_[i] != 0) {
      return false;
    }
  }
  return true;
};

var isNegative = function(self) {
  return self.sign_ == -1;
};

var isOdd = function(self) {
  return (self.bits_.length == 0) && (self.sign_ == -1) ||
         (self.bits_.length > 0) && ((self.bits_[0] & 1) != 0);
};

var I_equals = function(self, other) {
  if (self.sign_ != other.sign_) {
    return false;
  }
  var len = Math.max(self.bits_.length, other.bits_.length);
  for (var i = 0; i < len; i++) {
    if (I_getBits(self, i) != I_getBits(other, i)) {
      return false;
    }
  }
  return true;
};

var I_notEquals = function(self, other) {
  return !I_equals(self, other);
};

var I_greaterThan = function(self, other) {
  return I_compare(self, other) > 0;
};

var I_greaterThanOrEqual = function(self, other) {
  return I_compare(self, other) >= 0;
};

var I_lessThan = function(self, other) {
  return I_compare(self, other) < 0;
};

var I_lessThanOrEqual = function(self, other) {
  return I_compare(self, other) <= 0;
};

var I_compare = function(self, other) {
  var diff = I_sub(self, other);
  if (isNegative(diff)) {
    return -1;
  } else if (isZero(diff)) {
    return 0;
  } else {
    return +1;
  }
};

var I_compareInt = function(self, other) {
  return I_compare(self, I_fromInt(other));
}

var shorten = function(self, numBits) {
  var arr_index = (numBits - 1) >> 5;
  var bit_index = (numBits - 1) % 32;
  var bits = [];
  for (var i = 0; i < arr_index; i++) {
    bits[i] = I_getBits(self, i);
  }
  var sigBits = bit_index == 31 ? 0xFFFFFFFF : (1 << (bit_index + 1)) - 1;
  var val = I_getBits(self, arr_index) & sigBits;
  if (val & (1 << bit_index)) {
    val |= 0xFFFFFFFF - sigBits;
    bits[arr_index] = val;
    return new Integer(bits, -1);
  } else {
    bits[arr_index] = val;
    return new Integer(bits, 0);
  }
};

var I_negate = function(self) {
  return I_add(not(self), Integer.ONE);
};

var I_add = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  var carry = 0;

  for (var i = 0; i <= len; i++) {
    var a1 = I_getBits(self, i) >>> 16;
    var a0 = I_getBits(self, i) & 0xFFFF;

    var b1 = I_getBits(other, i) >>> 16;
    var b0 = I_getBits(other, i) & 0xFFFF;

    var c0 = carry + a0 + b0;
    var c1 = (c0 >>> 16) + a1 + b1;
    carry = c1 >>> 16;
    c0 &= 0xFFFF;
    c1 &= 0xFFFF;
    arr[i] = (c1 << 16) | c0;
  }
  return I_fromBits(arr);
};

var I_sub = function(self, other) {
  return I_add(self, I_negate(other));
};

var I_mul = function(self, other) {
  if (isZero(self)) {
    return Integer.ZERO;
  } else if (isZero(other)) {
    return Integer.ZERO;
  }

  if (isNegative(self)) {
    if (isNegative(other)) {
      return I_mul(I_negate(self), I_negate(other));
    } else {
      return I_negate(I_mul(I_negate(self), other));
    }
  } else if (isNegative(other)) {
    return I_negate(I_mul(self, I_negate(other)));
  }

  if (I_lessThan(self, Integer.TWO_PWR_24_) &&
      I_lessThan(other, Integer.TWO_PWR_24_)) {
    return I_fromNumber(I_toNumber(self) * I_toNumber(other));
  }

  var len = self.bits_.length + other.bits_.length;
  var arr = [];
  for (var i = 0; i < 2 * len; i++) {
    arr[i] = 0;
  }
  for (var i = 0; i < self.bits_.length; i++) {
    for (var j = 0; j < other.bits_.length; j++) {
      var a1 = I_getBits(self, i) >>> 16;
      var a0 = I_getBits(self, i) & 0xFFFF;

      var b1 = I_getBits(other, j) >>> 16;
      var b0 = I_getBits(other, j) & 0xFFFF;

      arr[2 * i + 2 * j] += a0 * b0;
      Integer.carry16_(arr, 2 * i + 2 * j);
      arr[2 * i + 2 * j + 1] += a1 * b0;
      Integer.carry16_(arr, 2 * i + 2 * j + 1);
      arr[2 * i + 2 * j + 1] += a0 * b1;
      Integer.carry16_(arr, 2 * i + 2 * j + 1);
      arr[2 * i + 2 * j + 2] += a1 * b1;
      Integer.carry16_(arr, 2 * i + 2 * j + 2);
    }
  }

  for (var i = 0; i < len; i++) {
    arr[i] = (arr[2 * i + 1] << 16) | arr[2 * i];
  }
  for (var i = len; i < 2 * len; i++) {
    arr[i] = 0;
  }
  return new Integer(arr, 0);
};

Integer.carry16_ = function(bits, index) {
  while ((bits[index] & 0xFFFF) != bits[index]) {
    bits[index + 1] += bits[index] >>> 16;
    bits[index] &= 0xFFFF;
  }
};

var I_mod = function(self, other) {
  return I_rem(I_add(other, I_rem(self, other)), other);
}

var I_div = function(self, other) {
  if(I_greaterThan(self, Integer.ZERO) != I_greaterThan(other, Integer.ZERO)) {
    if(I_rem(self, other) != Integer.ZERO) {
      return I_sub(I_quot(self, other), Integer.ONE);
    }
  }
  return I_quot(self, other);
}

var I_quotRem = function(self, other) {
  return [0, I_quot(self, other), I_rem(self, other)];
}

var I_divMod = function(self, other) {
  return [0, I_div(self, other), I_mod(self, other)];
}

var I_quot = function(self, other) {
  if (isZero(other)) {
    throw Error('division by zero');
  } else if (isZero(self)) {
    return Integer.ZERO;
  }

  if (isNegative(self)) {
    if (isNegative(other)) {
      return I_quot(I_negate(self), I_negate(other));
    } else {
      return I_negate(I_quot(I_negate(self), other));
    }
  } else if (isNegative(other)) {
    return I_negate(I_quot(self, I_negate(other)));
  }

  var res = Integer.ZERO;
  var rem = self;
  while (I_greaterThanOrEqual(rem, other)) {
    var approx = Math.max(1, Math.floor(I_toNumber(rem) / I_toNumber(other)));
    var log2 = Math.ceil(Math.log(approx) / Math.LN2);
    var delta = (log2 <= 48) ? 1 : Math.pow(2, log2 - 48);
    var approxRes = I_fromNumber(approx);
    var approxRem = I_mul(approxRes, other);
    while (isNegative(approxRem) || I_greaterThan(approxRem, rem)) {
      approx -= delta;
      approxRes = I_fromNumber(approx);
      approxRem = I_mul(approxRes, other);
    }

    if (isZero(approxRes)) {
      approxRes = Integer.ONE;
    }

    res = I_add(res, approxRes);
    rem = I_sub(rem, approxRem);
  }
  return res;
};

var I_rem = function(self, other) {
  return I_sub(self, I_mul(I_quot(self, other), other));
};

var not = function(self) {
  var len = self.bits_.length;
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = ~self.bits_[i];
  }
  return new Integer(arr, ~self.sign_);
};

var I_and = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) & I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ & other.sign_);
};

var I_or = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) | I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ | other.sign_);
};

var I_xor = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) ^ I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ ^ other.sign_);
};

var I_shiftLeft = function(self, numBits) {
  var arr_delta = numBits >> 5;
  var bit_delta = numBits % 32;
  var len = self.bits_.length + arr_delta + (bit_delta > 0 ? 1 : 0);
  var arr = [];
  for (var i = 0; i < len; i++) {
    if (bit_delta > 0) {
      arr[i] = (I_getBits(self, i - arr_delta) << bit_delta) |
               (I_getBits(self, i - arr_delta - 1) >>> (32 - bit_delta));
    } else {
      arr[i] = I_getBits(self, i - arr_delta);
    }
  }
  return new Integer(arr, self.sign_);
};

var I_shiftRight = function(self, numBits) {
  var arr_delta = numBits >> 5;
  var bit_delta = numBits % 32;
  var len = self.bits_.length - arr_delta;
  var arr = [];
  for (var i = 0; i < len; i++) {
    if (bit_delta > 0) {
      arr[i] = (I_getBits(self, i + arr_delta) >>> bit_delta) |
               (I_getBits(self, i + arr_delta + 1) << (32 - bit_delta));
    } else {
      arr[i] = I_getBits(self, i + arr_delta);
    }
  }
  return new Integer(arr, self.sign_);
};

var I_signum = function(self) {
  var cmp = I_compare(self, Integer.ZERO);
  if(cmp > 0) {
    return Integer.ONE
  }
  if(cmp < 0) {
    return I_sub(Integer.ZERO, Integer.ONE);
  }
  return Integer.ZERO;
};

var I_abs = function(self) {
  if(I_compare(self, Integer.ZERO) < 0) {
    return I_sub(Integer.ZERO, self);
  }
  return self;
};

var I_decodeDouble = function(x) {
  var dec = decodeDouble(x);
  var mantissa = I_fromBits([dec[3], dec[2]]);
  if(dec[1] < 0) {
    mantissa = I_negate(mantissa);
  }
  return [0, dec[4], mantissa];
}

var I_toString = function(self) {
  var radix = 10;

  if (isZero(self)) {
    return '0';
  } else if (isNegative(self)) {
    return '-' + I_toString(I_negate(self));
  }

  var radixToPower = I_fromNumber(Math.pow(radix, 6));

  var rem = self;
  var result = '';
  while (true) {
    var remDiv = I_div(rem, radixToPower);
    var intval = I_toInt(I_sub(rem, I_mul(remDiv, radixToPower)));
    var digits = intval.toString();

    rem = remDiv;
    if (isZero(rem)) {
      return digits + result;
    } else {
      while (digits.length < 6) {
        digits = '0' + digits;
      }
      result = '' + digits + result;
    }
  }
};

var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    return I_fromBits([x.getLowBits(), x.getHighBits()]);
}

function I_toInt64(x) {
    return Long.fromBits(I_getBits(x, 0), I_getBits(x, 1));
}

function I_fromWord64(x) {
    return x;
}

function I_toWord64(x) {
    return I_rem(I_add(__w64_max, x), __w64_max);
}

// Copyright 2009 The Closure Library Authors. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS-IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

var Long = function(low, high) {
  this.low_ = low | 0;
  this.high_ = high | 0;
};

Long.IntCache_ = {};

Long.fromInt = function(value) {
  if (-128 <= value && value < 128) {
    var cachedObj = Long.IntCache_[value];
    if (cachedObj) {
      return cachedObj;
    }
  }

  var obj = new Long(value | 0, value < 0 ? -1 : 0);
  if (-128 <= value && value < 128) {
    Long.IntCache_[value] = obj;
  }
  return obj;
};

Long.fromNumber = function(value) {
  if (isNaN(value) || !isFinite(value)) {
    return Long.ZERO;
  } else if (value <= -Long.TWO_PWR_63_DBL_) {
    return Long.MIN_VALUE;
  } else if (value + 1 >= Long.TWO_PWR_63_DBL_) {
    return Long.MAX_VALUE;
  } else if (value < 0) {
    return Long.fromNumber(-value).negate();
  } else {
    return new Long(
        (value % Long.TWO_PWR_32_DBL_) | 0,
        (value / Long.TWO_PWR_32_DBL_) | 0);
  }
};

Long.fromBits = function(lowBits, highBits) {
  return new Long(lowBits, highBits);
};

Long.TWO_PWR_16_DBL_ = 1 << 16;
Long.TWO_PWR_24_DBL_ = 1 << 24;
Long.TWO_PWR_32_DBL_ =
    Long.TWO_PWR_16_DBL_ * Long.TWO_PWR_16_DBL_;
Long.TWO_PWR_31_DBL_ =
    Long.TWO_PWR_32_DBL_ / 2;
Long.TWO_PWR_48_DBL_ =
    Long.TWO_PWR_32_DBL_ * Long.TWO_PWR_16_DBL_;
Long.TWO_PWR_64_DBL_ =
    Long.TWO_PWR_32_DBL_ * Long.TWO_PWR_32_DBL_;
Long.TWO_PWR_63_DBL_ =
    Long.TWO_PWR_64_DBL_ / 2;
Long.ZERO = Long.fromInt(0);
Long.ONE = Long.fromInt(1);
Long.NEG_ONE = Long.fromInt(-1);
Long.MAX_VALUE =
    Long.fromBits(0xFFFFFFFF | 0, 0x7FFFFFFF | 0);
Long.MIN_VALUE = Long.fromBits(0, 0x80000000 | 0);
Long.TWO_PWR_24_ = Long.fromInt(1 << 24);

Long.prototype.toInt = function() {
  return this.low_;
};

Long.prototype.toNumber = function() {
  return this.high_ * Long.TWO_PWR_32_DBL_ +
         this.getLowBitsUnsigned();
};

Long.prototype.getHighBits = function() {
  return this.high_;
};

Long.prototype.getLowBits = function() {
  return this.low_;
};

Long.prototype.getLowBitsUnsigned = function() {
  return (this.low_ >= 0) ?
      this.low_ : Long.TWO_PWR_32_DBL_ + this.low_;
};

Long.prototype.isZero = function() {
  return this.high_ == 0 && this.low_ == 0;
};

Long.prototype.isNegative = function() {
  return this.high_ < 0;
};

Long.prototype.isOdd = function() {
  return (this.low_ & 1) == 1;
};

Long.prototype.equals = function(other) {
  return (this.high_ == other.high_) && (this.low_ == other.low_);
};

Long.prototype.notEquals = function(other) {
  return (this.high_ != other.high_) || (this.low_ != other.low_);
};

Long.prototype.lessThan = function(other) {
  return this.compare(other) < 0;
};

Long.prototype.lessThanOrEqual = function(other) {
  return this.compare(other) <= 0;
};

Long.prototype.greaterThan = function(other) {
  return this.compare(other) > 0;
};

Long.prototype.greaterThanOrEqual = function(other) {
  return this.compare(other) >= 0;
};

Long.prototype.compare = function(other) {
  if (this.equals(other)) {
    return 0;
  }

  var thisNeg = this.isNegative();
  var otherNeg = other.isNegative();
  if (thisNeg && !otherNeg) {
    return -1;
  }
  if (!thisNeg && otherNeg) {
    return 1;
  }

  if (this.subtract(other).isNegative()) {
    return -1;
  } else {
    return 1;
  }
};

Long.prototype.negate = function() {
  if (this.equals(Long.MIN_VALUE)) {
    return Long.MIN_VALUE;
  } else {
    return this.not().add(Long.ONE);
  }
};

Long.prototype.add = function(other) {
  var a48 = this.high_ >>> 16;
  var a32 = this.high_ & 0xFFFF;
  var a16 = this.low_ >>> 16;
  var a00 = this.low_ & 0xFFFF;

  var b48 = other.high_ >>> 16;
  var b32 = other.high_ & 0xFFFF;
  var b16 = other.low_ >>> 16;
  var b00 = other.low_ & 0xFFFF;

  var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
  c00 += a00 + b00;
  c16 += c00 >>> 16;
  c00 &= 0xFFFF;
  c16 += a16 + b16;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c32 += a32 + b32;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c48 += a48 + b48;
  c48 &= 0xFFFF;
  return Long.fromBits((c16 << 16) | c00, (c48 << 16) | c32);
};

Long.prototype.subtract = function(other) {
  return this.add(other.negate());
};

Long.prototype.multiply = function(other) {
  if (this.isZero()) {
    return Long.ZERO;
  } else if (other.isZero()) {
    return Long.ZERO;
  }

  if (this.equals(Long.MIN_VALUE)) {
    return other.isOdd() ? Long.MIN_VALUE : Long.ZERO;
  } else if (other.equals(Long.MIN_VALUE)) {
    return this.isOdd() ? Long.MIN_VALUE : Long.ZERO;
  }

  if (this.isNegative()) {
    if (other.isNegative()) {
      return this.negate().multiply(other.negate());
    } else {
      return this.negate().multiply(other).negate();
    }
  } else if (other.isNegative()) {
    return this.multiply(other.negate()).negate();
  }

  if (this.lessThan(Long.TWO_PWR_24_) &&
      other.lessThan(Long.TWO_PWR_24_)) {
    return Long.fromNumber(this.toNumber() * other.toNumber());
  }

  var a48 = this.high_ >>> 16;
  var a32 = this.high_ & 0xFFFF;
  var a16 = this.low_ >>> 16;
  var a00 = this.low_ & 0xFFFF;

  var b48 = other.high_ >>> 16;
  var b32 = other.high_ & 0xFFFF;
  var b16 = other.low_ >>> 16;
  var b00 = other.low_ & 0xFFFF;

  var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
  c00 += a00 * b00;
  c16 += c00 >>> 16;
  c00 &= 0xFFFF;
  c16 += a16 * b00;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c16 += a00 * b16;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c32 += a32 * b00;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c32 += a16 * b16;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c32 += a00 * b32;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
  c48 &= 0xFFFF;
  return Long.fromBits((c16 << 16) | c00, (c48 << 16) | c32);
};

Long.prototype.div = function(other) {
  if (other.isZero()) {
    throw Error('division by zero');
  } else if (this.isZero()) {
    return Long.ZERO;
  }

  if (this.equals(Long.MIN_VALUE)) {
    if (other.equals(Long.ONE) ||
        other.equals(Long.NEG_ONE)) {
      return Long.MIN_VALUE;
    } else if (other.equals(Long.MIN_VALUE)) {
      return Long.ONE;
    } else {
      var halfThis = this.shiftRight(1);
      var approx = halfThis.div(other).shiftLeft(1);
      if (approx.equals(Long.ZERO)) {
        return other.isNegative() ? Long.ONE : Long.NEG_ONE;
      } else {
        var rem = this.subtract(other.multiply(approx));
        var result = approx.add(rem.div(other));
        return result;
      }
    }
  } else if (other.equals(Long.MIN_VALUE)) {
    return Long.ZERO;
  }

  if (this.isNegative()) {
    if (other.isNegative()) {
      return this.negate().div(other.negate());
    } else {
      return this.negate().div(other).negate();
    }
  } else if (other.isNegative()) {
    return this.div(other.negate()).negate();
  }

  var res = Long.ZERO;
  var rem = this;
  while (rem.greaterThanOrEqual(other)) {
    var approx = Math.max(1, Math.floor(rem.toNumber() / other.toNumber()));

    var log2 = Math.ceil(Math.log(approx) / Math.LN2);
    var delta = (log2 <= 48) ? 1 : Math.pow(2, log2 - 48);

    var approxRes = Long.fromNumber(approx);
    var approxRem = approxRes.multiply(other);
    while (approxRem.isNegative() || approxRem.greaterThan(rem)) {
      approx -= delta;
      approxRes = Long.fromNumber(approx);
      approxRem = approxRes.multiply(other);
    }

    if (approxRes.isZero()) {
      approxRes = Long.ONE;
    }

    res = res.add(approxRes);
    rem = rem.subtract(approxRem);
  }
  return res;
};

Long.prototype.modulo = function(other) {
  return this.subtract(this.div(other).multiply(other));
};

Long.prototype.not = function() {
  return Long.fromBits(~this.low_, ~this.high_);
};

Long.prototype.and = function(other) {
  return Long.fromBits(this.low_ & other.low_,
                                 this.high_ & other.high_);
};

Long.prototype.or = function(other) {
  return Long.fromBits(this.low_ | other.low_,
                                 this.high_ | other.high_);
};

Long.prototype.xor = function(other) {
  return Long.fromBits(this.low_ ^ other.low_,
                                 this.high_ ^ other.high_);
};

Long.prototype.shiftLeft = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var low = this.low_;
    if (numBits < 32) {
      var high = this.high_;
      return Long.fromBits(
          low << numBits,
          (high << numBits) | (low >>> (32 - numBits)));
    } else {
      return Long.fromBits(0, low << (numBits - 32));
    }
  }
};

Long.prototype.shiftRight = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var high = this.high_;
    if (numBits < 32) {
      var low = this.low_;
      return Long.fromBits(
          (low >>> numBits) | (high << (32 - numBits)),
          high >> numBits);
    } else {
      return Long.fromBits(
          high >> (numBits - 32),
          high >= 0 ? 0 : -1);
    }
  }
};

Long.prototype.shiftRightUnsigned = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var high = this.high_;
    if (numBits < 32) {
      var low = this.low_;
      return Long.fromBits(
          (low >>> numBits) | (high << (32 - numBits)),
          high >>> numBits);
    } else if (numBits == 32) {
      return Long.fromBits(high, 0);
    } else {
      return Long.fromBits(high >>> (numBits - 32), 0);
    }
  }
};



// Int64
function hs_eqInt64(x, y) {return x.equals(y);}
function hs_neInt64(x, y) {return !x.equals(y);}
function hs_ltInt64(x, y) {return x.compare(y) < 0;}
function hs_leInt64(x, y) {return x.compare(y) <= 0;}
function hs_gtInt64(x, y) {return x.compare(y) > 0;}
function hs_geInt64(x, y) {return x.compare(y) >= 0;}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shiftLeft(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shiftRight(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shiftRightUnsigned(bits);}
function hs_intToInt64(x) {return new Long(x, 0);}
function hs_int64ToInt(x) {return x.toInt();}



// Word64
function hs_wordToWord64(x) {
    return I_fromInt(x);
}
function hs_word64ToWord(x) {
    return I_toInt(x);
}
function hs_mkWord64(low, high) {
    return I_fromBits([low, high]);
}

var hs_and64 = I_and;
var hs_or64 = I_or;
var hs_xor64 = I_xor;
var __i64_all_ones = I_fromBits([0xffffffff, 0xffffffff]);
function hs_not64(x) {
    return I_xor(x, __i64_all_ones);
}
var hs_eqWord64 = I_equals;
var hs_neWord64 = I_notEquals;
var hs_ltWord64 = I_lessThan;
var hs_leWord64 = I_lessThanOrEqual;
var hs_gtWord64 = I_greaterThan;
var hs_geWord64 = I_greaterThanOrEqual;
var hs_quotWord64 = I_quot;
var hs_remWord64 = I_rem;
var __w64_max = I_fromBits([0,0,1]);
function hs_uncheckedShiftL64(x, bits) {
    return I_rem(I_shiftLeft(x, bits), __w64_max);
}
var hs_uncheckedShiftRL64 = I_shiftRight;
function hs_int64ToWord64(x) {
    var tmp = I_add(__w64_max, I_fromBits([x.getLowBits(), x.getHighBits()]));
    return I_rem(tmp, __w64_max);
}
function hs_word64ToInt64(x) {
    return Long.fromBits(I_getBits(x, 0), I_getBits(x, 1));
}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    var arr = {};
    var buffer = new ArrayBuffer(n);
    var views = {};
    views['i8']  = new Int8Array(buffer);
    views['i16'] = new Int16Array(buffer);
    views['i32'] = new Int32Array(buffer);
    views['w8']  = new Uint8Array(buffer);
    views['w16'] = new Uint16Array(buffer);
    views['w32'] = new Uint32Array(buffer);
    views['f32'] = new Float32Array(buffer);
    views['f64'] = new Float64Array(buffer);
    arr['b'] = buffer;
    arr['v'] = views;
    // ByteArray and Addr are the same thing, so keep an offset if we get
    // casted.
    arr['off'] = 0;
    return arr;
}
window['newByteArr'] = newByteArr;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return [0, 1, E(w).val];
}

function finalizeWeak(w) {
    return [0, B(A(E(w).fin, [0]))];
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as[0] === 1; as = as[2]) {
        arr.push(as[1]);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return [0];
    }
    return [1, arr[elem],new T(function(){return __arr2lst(elem+1,arr);})]
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs[0] === 1; xs = E(xs[2])) {
        arr.push(E(xs[1]));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0=(function(e){return e.getContext('2d');}),_1=(function(e){return !!e.getContext;}),_2=function(_3,_4,_){var _5=B(A(_3,[_])),_6=B(A(_4,[_]));return _5;},_7=function(_8,_9,_){var _a=B(A(_8,[_])),_b=B(A(_9,[_]));return new T(function(){return B(A(_a,[_b]));});},_c=function(_d,_e,_){var _f=B(A(_e,[_]));return _d;},_g=function(_h,_i,_){var _j=B(A(_i,[_]));return new T(function(){return B(A(_h,[_j]));});},_k=[0,_g,_c],_l=function(_m,_){return _m;},_n=function(_o,_p,_){var _q=B(A(_o,[_]));return new F(function(){return A(_p,[_]);});},_r=[0,_k,_l,_7,_n,_2],_s=function(_t,_u,_){var _v=B(A(_t,[_]));return new F(function(){return A(_u,[_v,_]);});},_w=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_x=new T(function(){return B(unCStr("base"));}),_y=new T(function(){return B(unCStr("IOException"));}),_z=[0],_A=new T(function(){var _B=hs_wordToWord64(4053623282),_C=hs_wordToWord64(3693590983);return [0,_B,_C,[0,_B,_C,_x,_w,_y],_z,_z];}),_D=function(_E){return E(_A);},_F=function(_G){return E(E(_G)[1]);},_H=function(_I,_J,_K){var _L=B(A(_I,[_])),_M=B(A(_J,[_])),_N=hs_eqWord64(_L[1],_M[1]);if(!_N){return [0];}else{var _O=hs_eqWord64(_L[2],_M[2]);return (!_O)?[0]:[1,_K];}},_P=function(_Q){var _R=E(_Q);return new F(function(){return _H(B(_F(_R[1])),_D,_R[2]);});},_S=new T(function(){return B(unCStr(": "));}),_T=new T(function(){return B(unCStr(")"));}),_U=new T(function(){return B(unCStr(" ("));}),_V=function(_W,_X){var _Y=E(_W);return (_Y[0]==0)?E(_X):[1,_Y[1],new T(function(){return B(_V(_Y[2],_X));})];},_Z=new T(function(){return B(unCStr("interrupted"));}),_10=new T(function(){return B(unCStr("system error"));}),_11=new T(function(){return B(unCStr("unsatisified constraints"));}),_12=new T(function(){return B(unCStr("user error"));}),_13=new T(function(){return B(unCStr("permission denied"));}),_14=new T(function(){return B(unCStr("illegal operation"));}),_15=new T(function(){return B(unCStr("end of file"));}),_16=new T(function(){return B(unCStr("resource exhausted"));}),_17=new T(function(){return B(unCStr("resource busy"));}),_18=new T(function(){return B(unCStr("does not exist"));}),_19=new T(function(){return B(unCStr("already exists"));}),_1a=new T(function(){return B(unCStr("resource vanished"));}),_1b=new T(function(){return B(unCStr("timeout"));}),_1c=new T(function(){return B(unCStr("unsupported operation"));}),_1d=new T(function(){return B(unCStr("hardware fault"));}),_1e=new T(function(){return B(unCStr("inappropriate type"));}),_1f=new T(function(){return B(unCStr("invalid argument"));}),_1g=new T(function(){return B(unCStr("failed"));}),_1h=new T(function(){return B(unCStr("protocol error"));}),_1i=function(_1j,_1k){switch(E(_1j)){case 0:return new F(function(){return _V(_19,_1k);});break;case 1:return new F(function(){return _V(_18,_1k);});break;case 2:return new F(function(){return _V(_17,_1k);});break;case 3:return new F(function(){return _V(_16,_1k);});break;case 4:return new F(function(){return _V(_15,_1k);});break;case 5:return new F(function(){return _V(_14,_1k);});break;case 6:return new F(function(){return _V(_13,_1k);});break;case 7:return new F(function(){return _V(_12,_1k);});break;case 8:return new F(function(){return _V(_11,_1k);});break;case 9:return new F(function(){return _V(_10,_1k);});break;case 10:return new F(function(){return _V(_1h,_1k);});break;case 11:return new F(function(){return _V(_1g,_1k);});break;case 12:return new F(function(){return _V(_1f,_1k);});break;case 13:return new F(function(){return _V(_1e,_1k);});break;case 14:return new F(function(){return _V(_1d,_1k);});break;case 15:return new F(function(){return _V(_1c,_1k);});break;case 16:return new F(function(){return _V(_1b,_1k);});break;case 17:return new F(function(){return _V(_1a,_1k);});break;default:return new F(function(){return _V(_Z,_1k);});}},_1l=new T(function(){return B(unCStr("}"));}),_1m=new T(function(){return B(unCStr("{handle: "));}),_1n=function(_1o,_1p,_1q,_1r,_1s,_1t){var _1u=new T(function(){var _1v=new T(function(){var _1w=new T(function(){var _1x=E(_1r);if(!_1x[0]){return E(_1t);}else{var _1y=new T(function(){return B(_V(_1x,new T(function(){return B(_V(_T,_1t));},1)));},1);return B(_V(_U,_1y));}},1);return B(_1i(_1p,_1w));}),_1z=E(_1q);if(!_1z[0]){return E(_1v);}else{return B(_V(_1z,new T(function(){return B(_V(_S,_1v));},1)));}}),_1A=E(_1s);if(!_1A[0]){var _1B=E(_1o);if(!_1B[0]){return E(_1u);}else{var _1C=E(_1B[1]);if(!_1C[0]){var _1D=new T(function(){var _1E=new T(function(){return B(_V(_1l,new T(function(){return B(_V(_S,_1u));},1)));},1);return B(_V(_1C[1],_1E));},1);return new F(function(){return _V(_1m,_1D);});}else{var _1F=new T(function(){var _1G=new T(function(){return B(_V(_1l,new T(function(){return B(_V(_S,_1u));},1)));},1);return B(_V(_1C[1],_1G));},1);return new F(function(){return _V(_1m,_1F);});}}}else{return new F(function(){return _V(_1A[1],new T(function(){return B(_V(_S,_1u));},1));});}},_1H=function(_1I){var _1J=E(_1I);return new F(function(){return _1n(_1J[1],_1J[2],_1J[3],_1J[4],_1J[6],_z);});},_1K=function(_1L,_1M,_1N){var _1O=E(_1M);return new F(function(){return _1n(_1O[1],_1O[2],_1O[3],_1O[4],_1O[6],_1N);});},_1P=function(_1Q,_1R){var _1S=E(_1Q);return new F(function(){return _1n(_1S[1],_1S[2],_1S[3],_1S[4],_1S[6],_1R);});},_1T=44,_1U=93,_1V=91,_1W=function(_1X,_1Y,_1Z){var _20=E(_1Y);if(!_20[0]){return new F(function(){return unAppCStr("[]",_1Z);});}else{var _21=new T(function(){var _22=new T(function(){var _23=function(_24){var _25=E(_24);if(!_25[0]){return [1,_1U,_1Z];}else{var _26=new T(function(){return B(A(_1X,[_25[1],new T(function(){return B(_23(_25[2]));})]));});return [1,_1T,_26];}};return B(_23(_20[2]));});return B(A(_1X,[_20[1],_22]));});return [1,_1V,_21];}},_27=function(_28,_29){return new F(function(){return _1W(_1P,_28,_29);});},_2a=[0,_1K,_1H,_27],_2b=new T(function(){return [0,_D,_2a,_2c,_P,_1H];}),_2c=function(_2d){return [0,_2b,_2d];},_2e=[0],_2f=7,_2g=function(_2h){return [0,_2e,_2f,_z,_2h,_2e,_2e];},_2i=function(_2j,_){var _2k=new T(function(){return B(_2c(new T(function(){return B(_2g(_2j));})));});return new F(function(){return die(_2k);});},_2l=[0,_r,_s,_n,_l,_2i],_2m=function(_2n){return E(_2n);},_2o=[0,_2l,_2m],_2p=(function(id){return document.getElementById(id);}),_2q=function(_){return new F(function(){return __jsNull();});},_2r=function(_2s){var _2t=B(A(_2s,[_]));return E(_2t);},_2u=new T(function(){return B(_2r(_2q));}),_2v=new T(function(){return E(_2u);}),_2w=function(_2x){return E(E(_2x)[2]);},_2y=function(_2z,_2A){var _2B=function(_){var _2C=E(_2p)(E(_2A)),_2D=__eq(_2C,E(_2v));return (E(_2D)==0)?[1,_2C]:_2e;};return new F(function(){return A(_2w,[_2z,_2B]);});},_2E=0,_2F=function(_){return _2E;},_2G=function(_2H,_2I,_){return new F(function(){return _2F(_);});},_2J="scroll",_2K="submit",_2L="blur",_2M="focus",_2N="change",_2O="unload",_2P="load",_2Q=function(_2R){switch(E(_2R)){case 0:return E(_2P);case 1:return E(_2O);case 2:return E(_2N);case 3:return E(_2M);case 4:return E(_2L);case 5:return E(_2K);default:return E(_2J);}},_2S=[0,_2Q,_2G],_2T="deltaZ",_2U="deltaY",_2V="deltaX",_2W=function(_2X,_2Y){var _2Z=jsShowI(_2X);return new F(function(){return _V(fromJSStr(_2Z),_2Y);});},_30=41,_31=40,_32=function(_33,_34,_35){if(_34>=0){return new F(function(){return _2W(_34,_35);});}else{if(_33<=6){return new F(function(){return _2W(_34,_35);});}else{return [1,_31,new T(function(){var _36=jsShowI(_34);return B(_V(fromJSStr(_36),[1,_30,_35]));})];}}},_37=new T(function(){return B(unCStr(")"));}),_38=new T(function(){return B(_32(0,2,_37));}),_39=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_38));}),_3a=function(_3b){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_32(0,_3b,_39));}))));});},_3c=function(_3d,_){return new T(function(){var _3e=Number(E(_3d)),_3f=jsTrunc(_3e);if(_3f<0){return B(_3a(_3f));}else{if(_3f>2){return B(_3a(_3f));}else{return _3f;}}});},_3g=0,_3h=[0,_3g,_3g,_3g],_3i="button",_3j=new T(function(){return jsGetMouseCoords;}),_3k=function(_3l,_){var _3m=E(_3l);if(!_3m[0]){return _z;}else{var _3n=B(_3k(_3m[2],_));return [1,new T(function(){var _3o=Number(E(_3m[1]));return jsTrunc(_3o);}),_3n];}},_3p=function(_3q,_){var _3r=__arr2lst(0,_3q);return new F(function(){return _3k(_3r,_);});},_3s=function(_3t,_){return new F(function(){return _3p(E(_3t),_);});},_3u=function(_3v,_){return new T(function(){var _3w=Number(E(_3v));return jsTrunc(_3w);});},_3x=[0,_3u,_3s],_3y=function(_3z,_){var _3A=E(_3z);if(!_3A[0]){return _z;}else{var _3B=B(_3y(_3A[2],_));return [1,_3A[1],_3B];}},_3C=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:272:5-9"));}),_3D=[0,_2e,_2f,_z,_3C,_2e,_2e],_3E=new T(function(){return B(_2c(_3D));}),_3F=function(_){return new F(function(){return die(_3E);});},_3G=function(_3H){return E(E(_3H)[1]);},_3I=function(_3J,_3K,_3L,_){var _3M=__arr2lst(0,_3L),_3N=B(_3y(_3M,_)),_3O=E(_3N);if(!_3O[0]){return new F(function(){return _3F(_);});}else{var _3P=E(_3O[2]);if(!_3P[0]){return new F(function(){return _3F(_);});}else{if(!E(_3P[2])[0]){var _3Q=B(A(_3G,[_3J,_3O[1],_])),_3R=B(A(_3G,[_3K,_3P[1],_]));return [0,_3Q,_3R];}else{return new F(function(){return _3F(_);});}}}},_3S=function(_3T,_3U,_){if(E(_3T)==7){var _3V=E(_3j)(_3U),_3W=B(_3I(_3x,_3x,_3V,_)),_3X=_3U[E(_2V)],_3Y=_3U[E(_2U)],_3Z=_3U[E(_2T)];return new T(function(){return [0,E(_3W),E(_2e),[0,_3X,_3Y,_3Z]];});}else{var _40=E(_3j)(_3U),_41=B(_3I(_3x,_3x,_40,_)),_42=_3U[E(_3i)],_43=__eq(_42,E(_2v));if(!E(_43)){var _44=B(_3c(_42,_));return new T(function(){return [0,E(_41),[1,_44],E(_3h)];});}else{return new T(function(){return [0,E(_41),E(_2e),E(_3h)];});}}},_45=function(_46,_47,_){return new F(function(){return _3S(_46,E(_47),_);});},_48="mouseout",_49="mouseover",_4a="mousemove",_4b="mouseup",_4c="mousedown",_4d="dblclick",_4e="click",_4f="wheel",_4g=function(_4h){switch(E(_4h)){case 0:return E(_4e);case 1:return E(_4d);case 2:return E(_4c);case 3:return E(_4b);case 4:return E(_4a);case 5:return E(_49);case 6:return E(_48);default:return E(_4f);}},_4i=[0,_4g,_45],_4j=function(_4k,_){return [1,_4k];},_4l=[0,_2m,_4j],_4m=[0,_2o,_l],_4n=0,_4o=new T(function(){return B(unCStr("Map.!: given key is not an element in the map"));}),_4p=new T(function(){return B(err(_4o));}),_4q=function(_4r){while(1){var _4s=E(_4r);if(!_4s[0]){switch(E(_4s[2])){case 0:_4r=_4s[5];continue;case 1:return E(_4s[3]);default:_4r=_4s[4];continue;}}else{return E(_4p);}}},_4t=function(_4u){while(1){var _4v=E(_4u);if(!_4v[0]){if(E(_4v[2])==2){return E(_4v[3]);}else{_4u=_4v[5];continue;}}else{return E(_4p);}}},_4w=function(_4x){while(1){var _4y=E(_4x);if(!_4y[0]){var _4z=_4y[4];switch(E(_4y[2])){case 0:return E(_4y[3]);case 1:_4x=_4z;continue;default:_4x=_4z;continue;}}else{return E(_4p);}}},_4A=function(_4B,_4C){var _4D=E(_4C);if(!_4D[0]){var _4E=_4D[2],_4F=_4D[3],_4G=_4D[4],_4H=_4D[5];switch(E(_4B)){case 0:switch(E(_4E)){case 0:return E(_4F);case 1:return new F(function(){return _4w(_4G);});break;default:return new F(function(){return _4w(_4G);});}break;case 1:switch(E(_4E)){case 0:return new F(function(){return _4q(_4H);});break;case 1:return E(_4F);default:return new F(function(){return _4q(_4G);});}break;default:if(E(_4E)==2){return E(_4F);}else{return new F(function(){return _4t(_4H);});}}}else{return E(_4p);}},_4I="src",_4J=(function(e,p,v){e[p] = v;}),_4K=(function(t){return document.createElement(t);}),_4L=function(_4M,_4N){return new F(function(){return A(_2w,[_4M,function(_){var _4O=E(_4K)("img"),_4P=E(_4J)(_4O,E(_4I),toJSStr(E(_4N)));return _4O;}]);});},_4Q=function(_4R,_){var _4S=E(_4R);if(!_4S[0]){return _z;}else{var _4T=B(A(_4L,[_2o,_4S[1],_])),_4U=B(_4Q(_4S[2],_));return [1,_4T,_4U];}},_4V=function(_4W,_4X,_){var _4Y=B(A(_4L,[_2o,_4W,_])),_4Z=B(_4Q(_4X,_));return [1,_4Y,_4Z];},_50=function(_51,_){return [0,_2E,_51];},_52=new T(function(){return B(unCStr("!!: negative index"));}),_53=new T(function(){return B(unCStr("Prelude."));}),_54=new T(function(){return B(_V(_53,_52));}),_55=new T(function(){return B(err(_54));}),_56=new T(function(){return B(unCStr("!!: index too large"));}),_57=new T(function(){return B(_V(_53,_56));}),_58=new T(function(){return B(err(_57));}),_59=function(_5a,_5b){while(1){var _5c=E(_5a);if(!_5c[0]){return E(_58);}else{var _5d=E(_5b);if(!_5d){return E(_5c[1]);}else{_5a=_5c[2];_5b=_5d-1|0;continue;}}}},_5e=function(_5f,_5g){if(_5g>=0){return new F(function(){return _59(_5f,_5g);});}else{return E(_55);}},_5h=function(_5i,_5j){return [0,E(_5i),E(_5j)];},_5k=new T(function(){return B(unCStr("GHC.Exception"));}),_5l=new T(function(){return B(unCStr("base"));}),_5m=new T(function(){return B(unCStr("ArithException"));}),_5n=new T(function(){var _5o=hs_wordToWord64(4194982440),_5p=hs_wordToWord64(3110813675);return [0,_5o,_5p,[0,_5o,_5p,_5l,_5k,_5m],_z,_z];}),_5q=function(_5r){return E(_5n);},_5s=function(_5t){var _5u=E(_5t);return new F(function(){return _H(B(_F(_5u[1])),_5q,_5u[2]);});},_5v=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_5w=new T(function(){return B(unCStr("denormal"));}),_5x=new T(function(){return B(unCStr("divide by zero"));}),_5y=new T(function(){return B(unCStr("loss of precision"));}),_5z=new T(function(){return B(unCStr("arithmetic underflow"));}),_5A=new T(function(){return B(unCStr("arithmetic overflow"));}),_5B=function(_5C,_5D){switch(E(_5C)){case 0:return new F(function(){return _V(_5A,_5D);});break;case 1:return new F(function(){return _V(_5z,_5D);});break;case 2:return new F(function(){return _V(_5y,_5D);});break;case 3:return new F(function(){return _V(_5x,_5D);});break;case 4:return new F(function(){return _V(_5w,_5D);});break;default:return new F(function(){return _V(_5v,_5D);});}},_5E=function(_5F){return new F(function(){return _5B(_5F,_z);});},_5G=function(_5H,_5I,_5J){return new F(function(){return _5B(_5I,_5J);});},_5K=function(_5L,_5M){return new F(function(){return _1W(_5B,_5L,_5M);});},_5N=[0,_5G,_5E,_5K],_5O=new T(function(){return [0,_5q,_5N,_5P,_5s,_5E];}),_5P=function(_5Q){return [0,_5O,_5Q];},_5R=3,_5S=new T(function(){return B(_5P(_5R));}),_5T=new T(function(){return die(_5S);}),_5U=(function(s){return s[0];}),_5V=function(_5W,_5X){var _5Y=_5W%_5X;if(_5W<=0){if(_5W>=0){return E(_5Y);}else{if(_5X<=0){return E(_5Y);}else{var _5Z=E(_5Y);return (_5Z==0)?0:_5Z+_5X|0;}}}else{if(_5X>=0){if(_5W>=0){return E(_5Y);}else{if(_5X<=0){return E(_5Y);}else{var _60=E(_5Y);return (_60==0)?0:_60+_5X|0;}}}else{var _61=E(_5Y);return (_61==0)?0:_61+_5X|0;}}},_62=(function(s){var ba = window['newByteArr'](16);ba['v']['w32'][0] = s[0];ba['v']['w32'][1] = s[1];ba['v']['w32'][2] = s[2];ba['v']['w32'][3] = s[3];return window['md51'](ba,16);}),_63=function(_64){return new F(function(){return _2r(function(_){return new F(function(){return E(_62)(E(_64));});});});},_65=function(_66,_67,_68){while(1){var _69=B((function(_6a,_6b,_6c){if(_6a>_6b){var _6d=_6b,_6e=_6a,_6f=_6c;_66=_6d;_67=_6e;_68=_6f;return null;}else{var _6g=new T(function(){var _6h=(_6b-_6a|0)+1|0;switch(_6h){case -1:return _6a;break;case 0:return E(_5T);break;default:return B(_5V(B(_2r(function(_){var _6i=E(_5U)(E(_6c));return new F(function(){return _3u(_6i,0);});})),_6h))+_6a|0;}});return [0,_6g,new T(function(){return B(_63(_6c));})];}})(_66,_67,_68));if(_69!=null){return _69;}}},_6j=function(_6k,_6l,_6m){var _6n=new T(function(){var _6o=E(_6k),_6p=E(_6o[1]),_6q=E(_6o[2]),_6r=E(_6l),_6s=new T(function(){var _6t=B(_65(0,2000000001,_6m));return [0,_6t[1],_6t[2]];}),_6u=new T(function(){var _6v=B(_65(0,2000000001,new T(function(){return E(E(_6s)[2]);})));return [0,_6v[1],_6v[2]];});return [0,[0,new T(function(){return E(E(_6s)[1])/2000000000*(E(_6r[1])-_6p)+_6p;}),new T(function(){return E(E(_6u)[1])/2000000000*(E(_6r[2])-_6q)+_6q;})],new T(function(){return E(E(_6u)[2]);})];});return [0,new T(function(){var _6w=E(E(_6n)[1]);return B(_5h(_6w[1],_6w[2]));}),new T(function(){return E(E(_6n)[2]);})];},_6x=function(_){return _2E;},_6y=(function(ctx,i,x,y){ctx.drawImage(i,x,y);}),_6z=function(_6A,_6B,_6C,_6D,_){var _6E=E(_6y)(_6D,_6A,_6B,_6C);return new F(function(){return _6x(_);});},_6F=function(_6G,_6H){while(1){var _6I=E(_6G);if(!_6I[0]){return E(_6H);}else{var _6J=_6I[2];switch(E(E(_6I[1])[5])){case 0:var _6K=_6H+1|0;_6G=_6J;_6H=_6K;continue;case 1:_6G=_6J;continue;default:_6G=_6J;continue;}}}},_6L=function(_6M,_6N){while(1){var _6O=E(_6M);if(!_6O[0]){return E(_6N);}else{var _6P=_6O[2];if(E(E(_6O[1])[5])==1){var _6Q=_6N+1|0;_6M=_6P;_6N=_6Q;continue;}else{_6M=_6P;continue;}}}},_6R=function(_6S,_6T){while(1){var _6U=E(_6S);if(!_6U[0]){return E(_6T);}else{var _6V=_6U[2];if(E(E(_6U[1])[5])==2){var _6W=_6T+1|0;_6S=_6V;_6T=_6W;continue;}else{_6S=_6V;continue;}}}},_6X=2,_6Y=0,_6Z=false,_70=1,_71=0,_72=0,_73=0,_74=true,_75=0,_76=1,_77=100,_78=function(_79,_){return _2E;},_7a=20,_7b=90,_7c=60,_7d=50,_7e=8,_7f=(function(e){e.width = e.width;}),_7g=new T(function(){return B(unCStr("findMax Nil"));}),_7h=new T(function(){return B(err(_7g));}),_7i=function(_7j){while(1){var _7k=E(_7j);switch(_7k[0]){case 0:_7j=_7k[4];continue;case 1:return [0,_7k[1],_7k[2]];default:return E(_7h);}}},_7l=function(_7m,_7n,_7o){var _7p=E(_7o);switch(_7p[0]){case 0:var _7q=_7p[1],_7r=_7p[2],_7s=_7p[3],_7t=_7p[4],_7u=_7r>>>0;if(((_7m>>>0&((_7u-1>>>0^4294967295)>>>0^_7u)>>>0)>>>0&4294967295)==_7q){return ((_7m>>>0&_7u)>>>0==0)?[0,_7q,_7r,E(B(_7l(_7m,_7n,_7s))),E(_7t)]:[0,_7q,_7r,E(_7s),E(B(_7l(_7m,_7n,_7t)))];}else{var _7v=(_7m>>>0^_7q>>>0)>>>0,_7w=(_7v|_7v>>>1)>>>0,_7x=(_7w|_7w>>>2)>>>0,_7y=(_7x|_7x>>>4)>>>0,_7z=(_7y|_7y>>>8)>>>0,_7A=(_7z|_7z>>>16)>>>0,_7B=(_7A^_7A>>>1)>>>0&4294967295,_7C=_7B>>>0;return ((_7m>>>0&_7C)>>>0==0)?[0,(_7m>>>0&((_7C-1>>>0^4294967295)>>>0^_7C)>>>0)>>>0&4294967295,_7B,[1,_7m,_7n],E(_7p)]:[0,(_7m>>>0&((_7C-1>>>0^4294967295)>>>0^_7C)>>>0)>>>0&4294967295,_7B,E(_7p),[1,_7m,_7n]];}break;case 1:var _7D=_7p[1];if(_7m!=_7D){var _7E=(_7m>>>0^_7D>>>0)>>>0,_7F=(_7E|_7E>>>1)>>>0,_7G=(_7F|_7F>>>2)>>>0,_7H=(_7G|_7G>>>4)>>>0,_7I=(_7H|_7H>>>8)>>>0,_7J=(_7I|_7I>>>16)>>>0,_7K=(_7J^_7J>>>1)>>>0&4294967295,_7L=_7K>>>0;return ((_7m>>>0&_7L)>>>0==0)?[0,(_7m>>>0&((_7L-1>>>0^4294967295)>>>0^_7L)>>>0)>>>0&4294967295,_7K,[1,_7m,_7n],E(_7p)]:[0,(_7m>>>0&((_7L-1>>>0^4294967295)>>>0^_7L)>>>0)>>>0&4294967295,_7K,E(_7p),[1,_7m,_7n]];}else{return [1,_7m,_7n];}break;default:return [1,_7m,_7n];}},_7M=function(_7N){var _7O=E(_7N);switch(_7O[0]){case 0:return B(_7M(_7O[3]))+B(_7M(_7O[4]))|0;case 1:return 1;default:return 0;}},_7P=new T(function(){return B(unCStr("findMax: empty map has no maximal element"));}),_7Q=new T(function(){return B(err(_7P));}),_7R=function(_7S,_7T){if(!B(_7M(_7T))){return new F(function(){return _7l(0,_7S,_7T);});}else{var _7U=E(_7T);switch(_7U[0]){case 0:if(_7U[2]>=0){return new F(function(){return _7l(E(B(_7i(_7U[4]))[1])+1|0,_7S,_7U);});}else{return new F(function(){return _7l(E(B(_7i(_7U[3]))[1])+1|0,_7S,_7U);});}break;case 1:return new F(function(){return _7l(_7U[1]+1|0,_7S,_7U);});break;default:return E(_7Q);}}},_7V=function(_7W,_7X){while(1){var _7Y=B((function(_7Z,_80){var _81=E(_80);switch(_81[0]){case 0:_7W=new T(function(){return B(_7V(_7Z,_81[4]));});_7X=_81[3];return null;case 1:return [1,_81[2],_7Z];default:return E(_7Z);}})(_7W,_7X));if(_7Y!=null){return _7Y;}}},_82=function(_83){var _84=E(_83);if(!_84[0]){var _85=_84[3],_86=_84[4];if(_84[2]>=0){return new F(function(){return _7V(new T(function(){return B(_7V(_z,_86));}),_85);});}else{return new F(function(){return _7V(new T(function(){return B(_7V(_z,_85));}),_86);});}}else{return new F(function(){return _7V(_z,_84);});}},_87=function(_88,_89){return E(_88)==E(_89);},_8a=function(_8b,_8c,_8d,_8e,_8f,_8g,_8h,_8i,_8j,_8k,_8l,_8m,_8n,_8o,_8p,_8q,_8r,_8s,_8t,_8u,_8v,_8w,_8x,_8y){if(_8b!=_8n){return false;}else{if(_8c!=_8o){return false;}else{if(E(_8d)!=E(_8p)){return false;}else{if(E(_8e)!=E(_8q)){return false;}else{if(E(_8f)!=E(_8r)){return false;}else{var _8z=function(_8A){var _8B=E(_8i),_8C=E(_8u);if(E(_8B[1])!=E(_8C[1])){return false;}else{if(E(_8B[2])!=E(_8C[2])){return false;}else{var _8D=function(_8E){if(E(_8k)!=E(_8w)){return false;}else{if(E(_8l)!=E(_8x)){return false;}else{return new F(function(){return _87(_8m,_8y);});}}};switch(E(_8j)){case 0:if(!E(_8v)){return new F(function(){return _8D(_);});}else{return false;}break;case 1:if(E(_8v)==1){return new F(function(){return _8D(_);});}else{return false;}break;default:if(E(_8v)==2){return new F(function(){return _8D(_);});}else{return false;}}}}};switch(E(_8g)){case 0:if(!E(_8s)){if(E(_8h)!=E(_8t)){return false;}else{return new F(function(){return _8z(_);});}}else{return false;}break;case 1:if(E(_8s)==1){if(E(_8h)!=E(_8t)){return false;}else{return new F(function(){return _8z(_);});}}else{return false;}break;default:if(E(_8s)==2){if(E(_8h)!=E(_8t)){return false;}else{return new F(function(){return _8z(_);});}}else{return false;}}}}}}}},_8F=function(_8G,_8H){var _8I=E(_8G),_8J=E(_8I[1]),_8K=E(_8H),_8L=E(_8K[1]);return (!B(_8a(E(_8J[1]),E(_8J[2]),_8I[2],_8I[3],_8I[4],_8I[5],_8I[6],_8I[7],_8I[8],_8I[9],_8I[10],_8I[11],E(_8L[1]),E(_8L[2]),_8K[2],_8K[3],_8K[4],_8K[5],_8K[6],_8K[7],_8K[8],_8K[9],_8K[10],_8K[11])))?true:false;},_8M=function(_8N,_8O){var _8P=E(_8N),_8Q=E(_8P[1]),_8R=E(_8O),_8S=E(_8R[1]);return new F(function(){return _8a(E(_8Q[1]),E(_8Q[2]),_8P[2],_8P[3],_8P[4],_8P[5],_8P[6],_8P[7],_8P[8],_8P[9],_8P[10],_8P[11],E(_8S[1]),E(_8S[2]),_8R[2],_8R[3],_8R[4],_8R[5],_8R[6],_8R[7],_8R[8],_8R[9],_8R[10],_8R[11]);});},_8T=[0,_8M,_8F],_8U=function(_8V){return E(E(_8V)[1]);},_8W=function(_8X,_8Y,_8Z){while(1){var _90=E(_8Y);if(!_90[0]){return (E(_8Z)[0]==0)?true:false;}else{var _91=E(_8Z);if(!_91[0]){return false;}else{if(!B(A(_8U,[_8X,_90[1],_91[1]]))){return false;}else{_8Y=_90[2];_8Z=_91[2];continue;}}}}},_92=function(_93,_94,_95,_){var _96=B(A(_94,[_95,_]));return [0,_93,new T(function(){return E(E(_96)[2]);})];},_97=function(_98,_99,_9a,_){var _9b=B(A(_99,[_9a,_])),_9c=new T(function(){return B(A(_98,[new T(function(){return E(E(_9b)[1]);})]));});return [0,_9c,new T(function(){return E(E(_9b)[2]);})];},_9d=[0,_97,_92],_9e=function(_9f,_9g,_){return [0,_9f,_9g];},_9h=function(_9i,_9j,_9k,_){var _9l=B(A(_9i,[_9k,_])),_9m=B(A(_9j,[new T(function(){return E(E(_9l)[2]);}),_])),_9n=new T(function(){return B(A(E(_9l)[1],[new T(function(){return E(E(_9m)[1]);})]));});return [0,_9n,new T(function(){return E(E(_9m)[2]);})];},_9o=function(_9p,_9q,_9r,_){var _9s=B(A(_9p,[_9r,_])),_9t=B(A(_9q,[new T(function(){return E(E(_9s)[2]);}),_]));return [0,new T(function(){return E(E(_9t)[1]);}),new T(function(){return E(E(_9t)[2]);})];},_9u=function(_9v,_9w,_9x,_){var _9y=B(A(_9v,[_9x,_])),_9z=B(A(_9w,[new T(function(){return E(E(_9y)[2]);}),_]));return [0,new T(function(){return E(E(_9y)[1]);}),new T(function(){return E(E(_9z)[2]);})];},_9A=[0,_9d,_9e,_9h,_9o,_9u],_9B=function(_9C,_9D,_9E,_){var _9F=B(A(_9C,[_9E,_]));return new F(function(){return A(_9D,[new T(function(){return E(E(_9F)[1]);}),new T(function(){return E(E(_9F)[2]);}),_]);});},_9G=function(_9H,_9I,_){return new F(function(){return _2i(_9H,_);});},_9J=function(_9K){return E(E(_9K)[2]);},_9L=function(_9M,_9N,_9O,_9P,_9Q){var _9R=function(_9S){return new F(function(){return A(_9P,[new T(function(){return E(E(_9S)[1]);}),new T(function(){return E(E(_9S)[2]);})]);});};return new F(function(){return A(_9J,[_9N,new T(function(){return B(A(_9O,[_9Q]));}),_9R]);});},_9T=function(_9U){return E(E(_9U)[5]);},_9V=function(_9W,_9X,_9Y){var _9Z=new T(function(){return B(A(_9T,[_9X,_9Y]));});return function(_a0){return E(_9Z);};},_a1=function(_a2){return E(E(_a2)[4]);},_a3=function(_a4,_a5){return [0,_a4,function(_a6,_a7,_a8){return new F(function(){return _9L(_a4,_a5,_a6,_a7,_a8);});},function(_a7,_a8){return new F(function(){return _a9(_a4,_a5,_a7,_a8);});},function(_aa,_ab){return new F(function(){return A(_a1,[_a5,[0,_aa,_ab]]);});},function(_a8){return new F(function(){return _9V(_a4,_a5,_a8);});}];},_a9=function(_ac,_ad,_ae,_af){return new F(function(){return A(_9J,[B(_a3(_ac,_ad)),_ae,function(_ag){return E(_af);}]);});},_ah=function(_ai,_aj){return new F(function(){return _a9(_9A,_2l,_ai,_aj);});},_ak=[0,_9A,_9B,_ah,_9e,_9G],_al=new T(function(){return B(unCStr(" is not an element of the map"));}),_am=function(_an){return new F(function(){return err(B(unAppCStr("IntMap.!: key ",new T(function(){return B(_V(B(_32(0,_an,_z)),_al));}))));});},_ao=function(_ap,_aq){var _ar=_ap;while(1){var _as=E(_ar);switch(_as[0]){case 0:var _at=_as[2]>>>0;if(((_aq>>>0&((_at-1>>>0^4294967295)>>>0^_at)>>>0)>>>0&4294967295)==_as[1]){if(!((_aq>>>0&_at)>>>0)){_ar=_as[3];continue;}else{_ar=_as[4];continue;}}else{return new F(function(){return _am(_aq);});}break;case 1:if(_aq!=_as[1]){return new F(function(){return _am(_aq);});}else{return E(_as[2]);}break;default:return new F(function(){return _am(_aq);});}}},_au=function(_av,_aw){if(_aw<=0){var _ax=function(_ay){var _az=function(_aA){var _aB=function(_aC){var _aD=function(_aE){var _aF=isDoubleNegativeZero(_aw),_aG=_aF,_aH=function(_aI){var _aJ=E(_av);if(!_aJ){return (_aw>=0)?(E(_aG)==0)?E(_aw):3.141592653589793:3.141592653589793;}else{var _aK=E(_aw);return (_aK==0)?E(_aJ):_aK+_aJ;}};if(!E(_aG)){return new F(function(){return _aH(_);});}else{var _aL=E(_av),_aM=isDoubleNegativeZero(_aL);if(!E(_aM)){return new F(function(){return _aH(_);});}else{return  -B(_au( -_aL,_aw));}}};if(_aw>=0){return new F(function(){return _aD(_);});}else{var _aN=E(_av),_aO=isDoubleNegativeZero(_aN);if(!E(_aO)){return new F(function(){return _aD(_);});}else{return  -B(_au( -_aN,_aw));}}};if(_aw>0){return new F(function(){return _aB(_);});}else{var _aP=E(_av);if(_aP>=0){return new F(function(){return _aB(_);});}else{return  -B(_au( -_aP,_aw));}}};if(_aw>=0){return new F(function(){return _az(_);});}else{var _aQ=E(_av);if(_aQ<=0){return new F(function(){return _az(_);});}else{return 3.141592653589793+Math.atan(_aQ/_aw);}}};if(!E(_aw)){if(E(_av)<=0){return new F(function(){return _ax(_);});}else{return 1.5707963267948966;}}else{return new F(function(){return _ax(_);});}}else{return new F(function(){return Math.atan(E(_av)/_aw);});}},_aR=function(_aS,_aT,_aU,_aV,_aW,_aX,_aY,_aZ,_b0,_b1,_b2,_b3,_b4,_b5,_b6,_b7,_){switch(E(_aW)){case 0:return (B(_6F(B(_82(_b3)),0))>=1000)?[0,_2E,[0,E(_b3),_b4,_b5,_b6,_b7]]:[0,_2E,new T(function(){return [0,E(B(_7R([0,_aS,_aT,_aU,_aV,_73,_aX,_aY,_aZ,_b0,_b1,_b2],_b3))),_b4,_b5,_b6,_b7];})];case 1:return (B(_6L(B(_82(_b3)),0))>=200)?[0,_2E,[0,E(_b3),_b4,_b5,_b6,_b7]]:[0,_2E,new T(function(){return [0,E(B(_7R([0,_aS,_aT,_aU,_aV,_70,_aX,_aY,_aZ,_b0,_b1,_b2],_b3))),_b4,_b5,_b6,_b7];})];default:return (B(_6R(B(_82(_b3)),0))>=50)?[0,_2E,[0,E(_b3),_b4,_b5,_b6,_b7]]:[0,_2E,new T(function(){return [0,E(B(_7R([0,_aS,_aT,_aU,_aV,_6X,_aX,_aY,_aZ,_b0,_b1,_b2],_b3))),_b4,_b5,_b6,_b7];})];}},_b8=function(_b9,_ba){while(1){if(_b9>=0){if(_b9<=640){if(_ba>=0){if(_ba<=480){return [0,_b9,_ba];}else{_ba=475;continue;}}else{_ba=5;continue;}}else{_b9=635;continue;}}else{_b9=5;continue;}}},_bb=(function(){var ba = window['newByteArr'](16);ba['v']['f64'][0] = Math.random();ba['v']['f64'][1] = Math.random();return window['md51'](ba,16);}),_bc=function(_bd,_be,_bf,_bg,_bh,_bi,_){var _bj=B(_ao(_be,_bd)),_bk=_bj[1],_bl=function(_bm,_bn,_bo,_bp,_bq,_){var _br=E(_bb)(),_bs=new T(function(){var _bt=new T(function(){var _bu=B(_ao(_bm,_bd)),_bv=new T(function(){return E(B(_6j(new T(function(){var _bw=E(_bk),_bx=B(_b8(E(_bw[1])-150,E(_bw[2])-150));return [0,E(_bx[1]),E(_bx[2])];},1),new T(function(){var _by=E(_bk),_bz=B(_b8(E(_by[1])+150,E(_by[2])+150));return [0,E(_bz[1]),E(_bz[2])];},1),_br))[1]);});return [0,_bu[1],_bu[2],_bu[3],_bu[4],_bu[5],_bu[6],_bv,_bu[8],_bu[9],_bu[10],_bu[11]];});return [0,E(B(_7l(_bd,_bt,_bm))),_bn,_bo,_bp,_bq];});return [0,_2E,_bs];};if(!E(B(_5V(E(_bj[6]),500)))){return new F(function(){return _bl(_be,_bf,_bg,_bh,_bi,_);});}else{var _bA=E(_bk),_bB=E(_bj[7]),_bC=E(_bA[1])-E(_bB[1]),_bD=E(_bA[2])-E(_bB[2]);if(Math.sqrt(_bC*_bC+_bD*_bD)>=10){return [0,_2E,[0,E(_be),_bf,_bg,_bh,_bi]];}else{return new F(function(){return _bl(_be,_bf,_bg,_bh,_bi,_);});}}},_bE=function(_bF){return E(E(_bF)[3]);},_bG=function(_bH,_bI,_bJ){if(0>=_bI){return new F(function(){return A(_a1,[_bH,_2E]);});}else{var _bK=B(_bE(_bH)),_bL=new T(function(){return B(A(_bK,[_bJ,new T(function(){return B(A(_a1,[_bH,_2E]));})]));}),_bM=function(_bN){var _bO=E(_bN);if(_bO==1){return E(_bL);}else{return new F(function(){return A(_bK,[_bJ,new T(function(){return B(_bM(_bO-1|0));})]);});}};return new F(function(){return _bM(_bI);});}},_bP=2,_bQ=1,_bR=function(_bS,_bT){switch(E(_bS)){case 0:return (E(_bT)==0)?false:true;case 1:return (E(_bT)==1)?false:true;default:return (E(_bT)==2)?false:true;}},_bU=function(_bV,_bW){switch(E(_bV)){case 0:return (E(_bW)==0)?true:false;case 1:return (E(_bW)==1)?true:false;default:return (E(_bW)==2)?true:false;}},_bX=[0,_bU,_bR],_bY=function(_bZ,_c0,_c1){while(1){var _c2=E(_c1);if(!_c2[0]){return false;}else{if(!B(A(_8U,[_bZ,_c0,_c2[1]]))){_c1=_c2[2];continue;}else{return true;}}}},_c3=function(_c4,_c5){while(1){var _c6=E(_c5);switch(_c6[0]){case 0:var _c7=_c6[3],_c8=B(_c3(_c4,_c6[4]));if(_c8[0]==2){_c5=_c7;continue;}else{var _c9=B(_c3(_c4,_c7));return (_c9[0]==2)?E(_c8):[0,_c6[1],_c6[2],E(_c9),E(_c8)];}break;case 1:return (!B(A(_c4,[_c6[1],_c6[2]])))?[2]:E(_c6);default:return [2];}}},_ca=[1,_z,_z],_cb=function(_cc,_cd){var _ce=function(_cf,_cg){var _ch=E(_cf);if(!_ch[0]){return E(_cg);}else{var _ci=_ch[1],_cj=E(_cg);if(!_cj[0]){return E(_ch);}else{var _ck=_cj[1];return (B(A(_cc,[_ci,_ck]))==2)?[1,_ck,new T(function(){return B(_ce(_ch,_cj[2]));})]:[1,_ci,new T(function(){return B(_ce(_ch[2],_cj));})];}}},_cl=function(_cm){var _cn=E(_cm);if(!_cn[0]){return [0];}else{var _co=E(_cn[2]);return (_co[0]==0)?E(_cn):[1,new T(function(){return B(_ce(_cn[1],_co[1]));}),new T(function(){return B(_cl(_co[2]));})];}},_cp=new T(function(){return B(_cq(B(_cl(_z))));}),_cq=function(_cr){while(1){var _cs=E(_cr);if(!_cs[0]){return E(_cp);}else{if(!E(_cs[2])[0]){return E(_cs[1]);}else{_cr=B(_cl(_cs));continue;}}}},_ct=new T(function(){return B(_cu(_z));}),_cv=function(_cw,_cx,_cy){while(1){var _cz=B((function(_cA,_cB,_cC){var _cD=E(_cC);if(!_cD[0]){return [1,[1,_cA,_cB],_ct];}else{var _cE=_cD[1];if(B(A(_cc,[_cA,_cE]))==2){var _cF=[1,_cA,_cB];_cw=_cE;_cx=_cF;_cy=_cD[2];return null;}else{return [1,[1,_cA,_cB],new T(function(){return B(_cu(_cD));})];}}})(_cw,_cx,_cy));if(_cz!=null){return _cz;}}},_cG=function(_cH,_cI,_cJ){while(1){var _cK=B((function(_cL,_cM,_cN){var _cO=E(_cN);if(!_cO[0]){return [1,new T(function(){return B(A(_cM,[[1,_cL,_z]]));}),_ct];}else{var _cP=_cO[1],_cQ=_cO[2];switch(B(A(_cc,[_cL,_cP]))){case 0:_cH=_cP;_cI=function(_cR){return new F(function(){return A(_cM,[[1,_cL,_cR]]);});};_cJ=_cQ;return null;case 1:_cH=_cP;_cI=function(_cS){return new F(function(){return A(_cM,[[1,_cL,_cS]]);});};_cJ=_cQ;return null;default:return [1,new T(function(){return B(A(_cM,[[1,_cL,_z]]));}),new T(function(){return B(_cu(_cO));})];}}})(_cH,_cI,_cJ));if(_cK!=null){return _cK;}}},_cu=function(_cT){var _cU=E(_cT);if(!_cU[0]){return E(_ca);}else{var _cV=_cU[1],_cW=E(_cU[2]);if(!_cW[0]){return [1,_cU,_z];}else{var _cX=_cW[1],_cY=_cW[2];if(B(A(_cc,[_cV,_cX]))==2){return new F(function(){return _cv(_cX,[1,_cV,_z],_cY);});}else{return new F(function(){return _cG(_cX,function(_cZ){return [1,_cV,_cZ];},_cY);});}}}};return new F(function(){return _cq(B(_cu(_cd)));});},_d0=function(_d1,_d2){while(1){var _d3=B((function(_d4,_d5){var _d6=E(_d5);switch(_d6[0]){case 0:_d1=new T(function(){return B(_d0(_d4,_d6[4]));});_d2=_d6[3];return null;case 1:return [1,[0,_d6[1],_d6[2]],_d4];default:return E(_d4);}})(_d1,_d2));if(_d3!=null){return _d3;}}},_d7=function(_d8){var _d9=E(_d8);if(!_d9[0]){var _da=_d9[3],_db=_d9[4];if(_d9[2]>=0){return new F(function(){return _d0(new T(function(){return B(_d0(_z,_db));}),_da);});}else{return new F(function(){return _d0(new T(function(){return B(_d0(_z,_da));}),_db);});}}else{return new F(function(){return _d0(_z,_d9);});}},_dc=function(_dd,_de,_df,_dg,_){var _dh=new T(function(){var _di=E(_dg)[1],_dj=new T(function(){return B(_ao(_di,E(_dd)));});return B(_cb(function(_dk,_dl){var _dm=E(E(E(_dk)[2])[1]),_dn=E(E(_dj)[1]),_do=E(_dn[1]),_dp=E(_dn[2]),_dq=E(E(E(_dl)[2])[1]),_dr=E(_dm[1])-_do,_ds=E(_dm[2])-_dp,_dt=Math.sqrt(_dr*_dr+_ds*_ds),_du=E(_dq[1])-_do,_dv=E(_dq[2])-_dp,_dw=Math.sqrt(_du*_du+_dv*_dv);return (_dt>=_dw)?(_dt!=_dw)?2:1:0;},B(_d7(B(_c3(function(_dx,_dy){var _dz=E(_dy),_dA=E(_dz[1]),_dB=E(E(_dj)[1]),_dC=E(_dA[1])-E(_dB[1]),_dD=E(_dA[2])-E(_dB[2]);if(Math.sqrt(_dC*_dC+_dD*_dD)>=E(_de)){return false;}else{return new F(function(){return _bY(_bX,_dz[5],_df);});}},_di))))));});return [0,_dh,_dg];},_dE=function(_dF,_dG,_dH,_dI){if(_dF!=_dH){return false;}else{return new F(function(){return _8M(_dG,_dI);});}},_dJ=function(_dK,_dL){var _dM=E(_dK),_dN=E(_dL);return new F(function(){return _dE(E(_dM[1]),_dM[2],E(_dN[1]),_dN[2]);});},_dO=function(_dP,_dQ,_dR,_dS){if(_dP!=_dR){return true;}else{var _dT=E(_dQ),_dU=E(_dT[1]),_dV=E(_dS),_dW=E(_dV[1]);return (!B(_8a(E(_dU[1]),E(_dU[2]),_dT[2],_dT[3],_dT[4],_dT[5],_dT[6],_dT[7],_dT[8],_dT[9],_dT[10],_dT[11],E(_dW[1]),E(_dW[2]),_dV[2],_dV[3],_dV[4],_dV[5],_dV[6],_dV[7],_dV[8],_dV[9],_dV[10],_dV[11])))?true:false;}},_dX=function(_dY,_dZ){var _e0=E(_dY),_e1=E(_dZ);return new F(function(){return _dO(E(_e0[1]),_e0[2],E(_e1[1]),_e1[2]);});},_e2=[0,_dJ,_dX],_e3=new T(function(){return B(unCStr(": empty list"));}),_e4=function(_e5){return new F(function(){return err(B(_V(_53,new T(function(){return B(_V(_e5,_e3));},1))));});},_e6=new T(function(){return B(unCStr("head"));}),_e7=new T(function(){return B(_e4(_e6));}),_e8=function(_e9,_ea){while(1){var _eb=B((function(_ec,_ed){var _ee=E(_ed);if(!_ee[0]){return [0];}else{var _ef=_ee[1],_eg=_ee[2];if(!B(A(_ec,[_ef]))){var _eh=_ec;_e9=_eh;_ea=_eg;return null;}else{return [1,_ef,new T(function(){return B(_e8(_ec,_eg));})];}}})(_e9,_ea));if(_eb!=null){return _eb;}}},_ei=10,_ej=function(_ek){return E(E(E(_ek)[2])[9])>0;},_el=[1,_70,_z],_em=[1,_73,_z],_en=function(_eo,_ep,_){var _eq=new T(function(){return B(_ao(E(_ep)[1],E(_eo)));}),_er=B(_dc(_eo,_ei,new T(function(){switch(E(E(_eq)[5])){case 0:return [0];break;case 1:return E(_em);break;default:return E(_el);}}),_ep,_)),_es=E(_er),_et=_es[2],_eu=B(_e8(_ej,_es[1]));if(!B(_8W(_e2,_eu,_z))){var _ev=new T(function(){var _ew=E(_et),_ex=_ew[1],_ey=E(_eo),_ez=E(_eu);if(!_ez[0]){return E(_e7);}else{var _eA=E(_ez[1]),_eB=E(_eA[1]),_eC=new T(function(){var _eD=B(_ao(_ex,_ey));return [0,_eD[1],_eD[2],_eD[3],_eD[4],_eD[5],_eD[6],_eD[7],_eD[8],new T(function(){var _eE=E(E(_eA[2])[3]);return E(_eD[9])+_eE*_eE/200;}),_eD[10],_eD[11]];}),_eF=B(_7l(_ey,_eC,_ex)),_eG=new T(function(){var _eH=B(_ao(_eF,_ey));return [0,_eH[1],_eH[2],_eH[3],_eH[4],_eH[5],_eH[6],_eH[7],_eH[8],new T(function(){var _eI=E(_eH[9]);if(100>_eI){return E(_eI);}else{return E(_77);}}),_eH[10],_eH[11]];}),_eJ=B(_7l(_ey,_eG,_eF)),_eK=new T(function(){var _eL=B(_ao(_eJ,_eB));return [0,_eL[1],_eL[2],_eL[3],_eL[4],_eL[5],_eL[6],_eL[7],_eL[8],new T(function(){var _eM=E(E(_eq)[3]);return E(_eL[9])-_eM*_eM*_eM/100000;}),_eL[10],_eL[11]];});return [0,E(B(_7l(_eB,_eK,_eJ))),_ew[2],_ew[3],_ew[4],_ew[5]];}});return [0,_6Z,_ev];}else{return [0,_74,_et];}},_eN=function(_eO){var _eP=I_decodeDouble(_eO);return [0,[1,_eP[2]],_eP[1]];},_eQ=function(_eR){var _eS=E(_eR);if(!_eS[0]){return _eS[1];}else{return new F(function(){return I_toNumber(_eS[1]);});}},_eT=480,_eU=640,_eV=[1,_6X,_z],_eW=function(_eX){return [0,_eX];},_eY=function(_eZ){var _f0=hs_intToInt64(2147483647),_f1=hs_leInt64(_eZ,_f0);if(!_f1){return [1,I_fromInt64(_eZ)];}else{var _f2=hs_intToInt64(-2147483648),_f3=hs_geInt64(_eZ,_f2);if(!_f3){return [1,I_fromInt64(_eZ)];}else{var _f4=hs_int64ToInt(_eZ);return new F(function(){return _eW(_f4);});}}},_f5=function(_f6){var _f7=hs_intToInt64(_f6);return E(_f7);},_f8=function(_f9){var _fa=E(_f9);if(!_fa[0]){return new F(function(){return _f5(_fa[1]);});}else{return new F(function(){return I_toInt64(_fa[1]);});}},_fb=function(_fc,_fd){var _fe=E(_fc);if(!_fe[0]){var _ff=_fe[1],_fg=E(_fd);return (_fg[0]==0)?_ff<_fg[1]:I_compareInt(_fg[1],_ff)>0;}else{var _fh=_fe[1],_fi=E(_fd);return (_fi[0]==0)?I_compareInt(_fh,_fi[1])<0:I_compare(_fh,_fi[1])<0;}},_fj=5,_fk=20,_fl=[0,E(_75),E(_75)],_fm=-0.2617993877991494,_fn=[0,0],_fo=function(_fp,_fq){var _fr=E(_fq);return (_fr[0]==0)?[0]:[1,new T(function(){return B(A(_fp,[_fr[1]]));}),new T(function(){return B(_fo(_fp,_fr[2]));})];},_fs=function(_ft,_fu){while(1){var _fv=E(_ft);if(!_fv[0]){_ft=[1,I_fromInt(_fv[1])];continue;}else{return [1,I_shiftLeft(_fv[1],_fu)];}}},_fw=function(_fx){return E(E(_fx)[2]);},_fy=function(_fz,_fA){while(1){var _fB=B((function(_fC,_fD){var _fE=E(_fD);switch(_fE[0]){case 0:_fz=new T(function(){return B(_fy(_fC,_fE[4]));});_fA=_fE[3];return null;case 1:var _fF=_fE[1],_fG=function(_fH,_fI,_fJ,_fK,_fL,_){return new F(function(){return _bc(_fF,B(_7l(_fF,new T(function(){var _fM=B(_ao(_fH,_fF));return [0,_fM[1],_fM[2],_fM[3],_fM[4],_fM[5],_fM[6],_fM[7],_71,_fM[9],_fM[10],_fM[11]];}),_fH)),_fI,_fJ,_fK,_fL,_);});},_fN=function(_fO,_){var _fP=E(_fO),_fQ=_fP[1],_fR=B(_ao(_fQ,_fF)),_fS=_fR[3],_fT=_fR[5],_fU=_fR[6],_fV=_fR[8],_fW=_fR[9],_fX=_fR[10],_fY=_fR[11],_fZ=E(_fR[7]),_g0=E(_fR[1]),_g1=E(_g0[1]),_g2=E(_g0[2]),_g3=E(_fR[4]),_g4=E(_fZ[1])-_g1,_g5=E(_fZ[2])-_g2,_g6=new T(function(){var _g7=B(_eN(B(_au(_g5,_g4))/0.2617993877991494)),_g8=_g7[1],_g9=_g7[2];if(_g9>=0){return 0.2617993877991494*B(_eQ(B(_fs(_g8,_g9))));}else{var _ga= -_g9;if(_ga<=52){var _gb=hs_uncheckedIShiftRA64(B(_f8(_g8)),_ga);return 0.2617993877991494*B(_eQ(B(_eY(_gb))));}else{if(!B(_fb(_g8,_fn))){return E(_75);}else{return E(_fm);}}}}),_gc=function(_,_gd,_ge,_gf,_gg,_gh,_gi,_gj,_gk,_gl,_gm,_gn,_go){var _gp=function(_,_gq,_gr,_gs,_gt,_gu,_gv,_gw,_gx,_gy,_gz,_gA,_gB){var _gC=new T(function(){return [0,E(B(_7l(_fF,[0,_gr,_gs,_gt,_gu,_gv,new T(function(){return E(_gw)+1|0;}),_gx,_gy,new T(function(){return E(_gz)-(E(_fS)/1000+_g3/1000)*E(_fY);}),_gA,_gB],_fQ))),_fP[2],_fP[3],_fP[4],_fP[5]];}),_gD=B(_en(_fF,_gC,_));switch(E(_fT)){case 0:var _gE=E(E(_gD)[2]),_gF=_gE[1],_gG=B(_ao(_gF,_fF)),_gH=_gG[1];if(!B(_5V(E(_gG[6]),150))){if(B(_7M(B(_c3(function(_gI,_gJ){var _gK=E(_gJ);switch(E(_gK[5])){case 0:var _gL=E(_gK[1]),_gM=E(_gH),_gN=E(_gL[1])-E(_gM[1]),_gO=E(_gL[2])-E(_gM[2]);return Math.sqrt(_gN*_gN+_gO*_gO)<100;case 1:return false;default:return false;}},_gF))))>=10){return new F(function(){return A(_fC,[_gE,_]);});}else{var _gP=new T(function(){var _gQ=E(_gH),_gR=E(_gQ[1]),_gS=E(_gQ[2]),_gT=_gR-30;if(_gT>0){var _gU=_gT;}else{var _gU=E(_75);}var _gV=_gS-30;if(_gV>0){var _gW=_gV;}else{var _gW=E(_75);}var _gX=_gR+30;if(_gX>640){var _gY=E(_eU);}else{var _gY=_gX;}var _gZ=_gS+30;if(_gZ>480){var _h0=E(_eT);}else{var _h0=_gZ;}return [0,[0,E(_gU),E(_gW)],[0,E(_gY),E(_h0)]];}),_h1=new T(function(){return E(E(_gP)[2]);}),_h2=new T(function(){return E(E(_gP)[1]);}),_h3=function(_h4,_){var _h5=E(_bb)(),_h6=E(_h4),_h7=_h6[1],_h8=_h6[2],_h9=_h6[3],_ha=_h6[4],_hb=_h6[5],_hc=new T(function(){return E(B(_6j(_h2,_h1,_h5))[1]);});return (B(_6F(B(_82(_h7)),0))>=1000)?[0,_2E,[0,E(_h7),_h8,_h9,_ha,_hb]]:[0,_2E,new T(function(){return [0,E(B(_7R([0,_hc,_75,_7e,_7a,_73,_4n,_hc,_71,_77,_76,_76],_h7))),_h8,_h9,_ha,_hb];})];},_hd=B(A(_bG,[_ak,3,_h3,_gE,_]));return new F(function(){return A(_fC,[new T(function(){return E(E(_hd)[2]);}),_]);});}}else{return new F(function(){return A(_fC,[_gE,_]);});}break;case 1:var _he=new T(function(){return E(E(_gD)[2]);}),_hf=B(_en(_fF,_he,_)),_hg=E(_hf),_hh=_hg[2];if(!E(_hg[1])){return new F(function(){return A(_fC,[_hh,_]);});}else{var _hi=B(_ao(E(_he)[1],_fF)),_hj=_hi[1],_hk=_hi[5];if(E(_hi[8])==2){return new F(function(){return A(_fC,[_hh,_]);});}else{var _hl=new T(function(){return E(_hi[10])*80;}),_hm=B(_dc(_fF,_hl,new T(function(){switch(E(_hk)){case 0:return [0];break;case 1:return E(_em);break;default:return E(_el);}}),_hh,_)),_hn=B(_dc(_fF,_fk,new T(function(){switch(E(_hk)){case 0:return [0];break;case 1:return E(_em);break;default:return E(_el);}}),new T(function(){return E(E(_hm)[2]);}),_)),_ho=B(_dc(_fF,_fj,new T(function(){switch(E(_hk)){case 0:return [0];break;case 1:return E(_em);break;default:return E(_el);}}),new T(function(){return E(E(_hn)[2]);}),_)),_hp=E(_ho),_hq=_hp[2],_hr=function(_,_hs){var _ht=new T(function(){return E(_hl)/2;}),_hu=new T(function(){return E(E(_hs)[2]);}),_hv=B(_dc(_fF,_ht,_eV,_hu,_)),_hw=E(_hv),_hx=_hw[2],_hy=B(_fo(_fw,_hw[1]));if(!B(_8W(_8T,_hy,_z))){var _hz=new T(function(){var _hA=E(_hx),_hB=_hA[1],_hC=new T(function(){var _hD=B(_ao(_hB,_fF)),_hE=new T(function(){var _hF=E(_hy);if(!_hF[0]){var _hG=B(_b8(0,0));return [0,E(_hG[1]),E(_hG[2])];}else{var _hH=E(B(_ao(E(_hu)[1],_fF))[1]),_hI=E(_hH[1]),_hJ=E(_hH[2]),_hK=E(E(_hF[1])[1]),_hL=E(_ht),_hM=_hI-E(_hK[1]),_hN=_hJ-E(_hK[2]),_hO=Math.sqrt(_hM*_hM+_hN*_hN),_hP=_hL-_hO,_hQ=function(_hR,_hS,_hT){while(1){var _hU=E(_hR);if(!_hU[0]){return [0,_hS,_hT];}else{var _hV=E(E(_hU[1])[1]),_hW=_hI-E(_hV[1]),_hX=_hJ-E(_hV[2]),_hY=Math.sqrt(_hW*_hW+_hX*_hX),_hZ=_hL-_hY,_i0=E(_hS)+_hW/_hY*_hZ,_i1=E(_hT)+_hX/_hY*_hZ;_hR=_hU[2];_hS=_i0;_hT=_i1;continue;}}},_i2=B(_hQ(_hF[2],_hM/_hO*_hP,_hN/_hO*_hP)),_i3=B(_b8(E(_i2[1]),E(_i2[2])));return [0,E(_i3[1]),E(_i3[2])];}});return [0,_hD[1],_hD[2],_hD[3],_hD[4],_hD[5],_hD[6],_hE,_hD[8],_hD[9],_hD[10],_hD[11]];});return [0,E(B(_7l(_fF,_hC,_hB))),_hA[2],_hA[3],_hA[4],_hA[5]];});return new F(function(){return A(_fC,[_hz,_]);});}else{return new F(function(){return A(_fC,[_hx,_]);});}};if(!B(_8W(_8T,B(_fo(_fw,_hp[1])),_z))){return new F(function(){return _hr(_,[0,_2E,_hq]);});}else{var _i4=B(_fo(_fw,E(_hn)[1]));if(!B(_8W(_8T,_i4,_z))){var _i5=new T(function(){var _i6=E(_hq),_i7=_i6[1],_i8=new T(function(){var _i9=B(_ao(_i7,_fF));return [0,_i9[1],_i9[2],_i9[3],_i9[4],_i9[5],_i9[6],new T(function(){var _ia=E(_i4);if(!_ia[0]){return E(_e7);}else{return E(E(_ia[1])[1]);}}),_i9[8],_i9[9],_i9[10],_i9[11]];});return [0,E(B(_7l(_fF,_i8,_i7))),_i6[2],_i6[3],_i6[4],_i6[5]];});return new F(function(){return _hr(_,[0,_2E,_i5]);});}else{var _ib=E(_hi[9]),_ic=function(_id){if(_ib<=80){var _ie=E(_hq),_if=B(_bc(_fF,_ie[1],_ie[2],_ie[3],_ie[4],_ie[5],_));return new F(function(){return _hr(_,_if);});}else{var _ig=E(_hi[6]);if(200>=_ig){var _ih=E(_hq),_ii=B(_bc(_fF,_ih[1],_ih[2],_ih[3],_ih[4],_ih[5],_));return new F(function(){return _hr(_,_ii);});}else{if(!B(_5V(_ig,500))){var _ij=function(_ik,_il,_im,_in,_io,_ip,_iq,_ir,_is,_it,_iu){var _iv=E(_hq),_iw=B(_aR(_ik,_il,_im,_in,_io,_ip,_iq,_ir,_is,_it,_iu,_iv[1],_iv[2],_iv[3],_iv[4],_iv[5],_));return new F(function(){return _hr(_,_iw);});};switch(E(_hk)){case 0:return new F(function(){return _ij(_hj,_75,_7e,_7a,_73,_4n,_fl,_71,_77,_76,_76);});break;case 1:return new F(function(){return _ij(_hj,_75,_7d,_7c,_70,_4n,_fl,_71,_77,_76,_76);});break;default:return new F(function(){return _ij(_hj,_75,_7b,_7c,_6X,_4n,_fl,_71,_77,_76,_76);});}}else{var _ix=E(_hq),_iy=B(_bc(_fF,_ix[1],_ix[2],_ix[3],_ix[4],_ix[5],_));return new F(function(){return _hr(_,_iy);});}}}};if(_ib>=50){return new F(function(){return _ic(_);});}else{var _iz=B(_fo(_fw,E(_hm)[1]));if(!B(_8W(_8T,_iz,_z))){var _iA=new T(function(){var _iB=E(_hq),_iC=_iB[1],_iD=new T(function(){var _iE=B(_ao(_iC,_fF));return [0,_iE[1],_iE[2],_iE[3],_iE[4],_iE[5],_iE[6],new T(function(){var _iF=E(_iz);if(!_iF[0]){return E(_e7);}else{return E(E(_iF[1])[1]);}}),_iE[8],_iE[9],_iE[10],_iE[11]];});return [0,E(B(_7l(_fF,_iD,_iC))),_iB[2],_iB[3],_iB[4],_iB[5]];});return new F(function(){return _hr(_,[0,_2E,_iA]);});}else{return new F(function(){return _ic(_);});}}}}}}break;default:var _iG=new T(function(){return E(E(_gD)[2]);}),_iH=B(_en(_fF,_iG,_)),_iI=E(_iH),_iJ=_iI[2];if(!E(_iI[1])){return new F(function(){return A(_fC,[_iJ,_]);});}else{var _iK=B(_ao(E(_iG)[1],_fF)),_iL=_iK[1],_iM=_iK[5];if(E(_iK[8])==2){return new F(function(){return A(_fC,[_iJ,_]);});}else{var _iN=B(_dc(_fF,new T(function(){return E(_iK[10])*40;}),new T(function(){switch(E(_iM)){case 0:return [0];break;case 1:return E(_em);break;default:return E(_el);}}),_iJ,_)),_iO=B(_dc(_fF,_fk,new T(function(){switch(E(_iM)){case 0:return [0];break;case 1:return E(_em);break;default:return E(_el);}}),new T(function(){return E(E(_iN)[2]);}),_)),_iP=B(_dc(_fF,_fj,new T(function(){switch(E(_iM)){case 0:return [0];break;case 1:return E(_em);break;default:return E(_el);}}),new T(function(){return E(E(_iO)[2]);}),_)),_iQ=E(_iP),_iR=_iQ[2];if(!B(_8W(_8T,B(_fo(_fw,_iQ[1])),_z))){return new F(function(){return A(_fC,[_iR,_]);});}else{var _iS=B(_fo(_fw,E(_iO)[1]));if(!B(_8W(_8T,_iS,_z))){var _iT=new T(function(){var _iU=E(_iR),_iV=_iU[1],_iW=new T(function(){var _iX=B(_ao(_iV,_fF));return [0,_iX[1],_iX[2],_iX[3],_iX[4],_iX[5],_iX[6],new T(function(){var _iY=E(_iS);if(!_iY[0]){return E(_e7);}else{return E(E(_iY[1])[1]);}}),_iX[8],_iX[9],_iX[10],_iX[11]];});return [0,E(B(_7l(_fF,_iW,_iV))),_iU[2],_iU[3],_iU[4],_iU[5]];});return new F(function(){return A(_fC,[_iT,_]);});}else{var _iZ=E(_iK[9]),_j0=function(_j1,_j2,_j3,_j4,_j5,_){var _j6=function(_j7,_j8,_j9,_ja,_jb,_jc,_jd,_je,_jf,_jg,_jh){return new F(function(){return _aR(_j7,_j8,_j9,_ja,_jb,_jc,_jd,_je,_jf,_jg,_jh,B(_7l(_fF,new T(function(){var _ji=B(_ao(_j1,_fF));return [0,_ji[1],_ji[2],_ji[3],_ji[4],_ji[5],_ji[6],_ji[7],_71,_ji[9],_ji[10],_ji[11]];}),_j1)),_j2,_j3,_j4,_j5,_);});};switch(E(_iM)){case 0:return new F(function(){return _j6(_iL,_75,_7e,_7a,_73,_4n,_fl,_71,_77,_76,_76);});break;case 1:return new F(function(){return _j6(_iL,_75,_7d,_7c,_70,_4n,_fl,_71,_77,_76,_76);});break;default:return new F(function(){return _j6(_iL,_75,_7b,_7c,_6X,_4n,_fl,_71,_77,_76,_76);});}},_jj=new T(function(){if(_iZ<=80){return false;}else{var _jk=E(_iK[6]);if(200>=_jk){return false;}else{if(!B(_5V(_jk,500))){return true;}else{return false;}}}});if(_iZ>=70){if(!E(_jj)){var _jl=E(_iR),_jm=B(_fG(_jl[1],_jl[2],_jl[3],_jl[4],_jl[5],_));return new F(function(){return A(_fC,[new T(function(){return E(E(_jm)[2]);}),_]);});}else{var _jn=E(_iR),_jo=B(_j0(_jn[1],_jn[2],_jn[3],_jn[4],_jn[5],_));return new F(function(){return A(_fC,[new T(function(){return E(E(_jo)[2]);}),_]);});}}else{var _jp=B(_fo(_fw,E(_iN)[1]));if(!B(_8W(_8T,_jp,_z))){var _jq=new T(function(){var _jr=E(_iR),_js=_jr[1],_jt=B(_7l(_fF,new T(function(){var _ju=B(_ao(_js,_fF));return [0,_ju[1],_ju[2],_ju[3],_ju[4],_ju[5],_ju[6],_ju[7],_bQ,_ju[9],_ju[10],_ju[11]];}),_js)),_jv=new T(function(){var _jw=B(_ao(_jt,_fF));return [0,_jw[1],_jw[2],_jw[3],_jw[4],_jw[5],_jw[6],new T(function(){var _jx=E(_jp);if(!_jx[0]){return E(_e7);}else{return E(E(_jx[1])[1]);}}),_jw[8],_jw[9],_jw[10],_jw[11]];});return [0,E(B(_7l(_fF,_jv,_jt))),_jr[2],_jr[3],_jr[4],_jr[5]];});return new F(function(){return A(_fC,[_jq,_]);});}else{if(!E(_jj)){var _jy=E(_iR),_jz=B(_fG(_jy[1],_jy[2],_jy[3],_jy[4],_jy[5],_));return new F(function(){return A(_fC,[new T(function(){return E(E(_jz)[2]);}),_]);});}else{var _jA=E(_iR),_jB=B(_j0(_jA[1],_jA[2],_jA[3],_jA[4],_jA[5],_));return new F(function(){return A(_fC,[new T(function(){return E(E(_jB)[2]);}),_]);});}}}}}}}}};if(E(_fW)>=0){return new F(function(){return _gp(_,_2E,_ge,_gf,_gg,_gh,_gi,_gj,_gk,_gl,_gm,_gn,_go);});}else{return new F(function(){return _gp(_,_2E,_ge,_gf,_gg,_gh,_gi,_gj,_gk,_bP,_gm,_gn,_go);});}};if(_g3<=20){return new F(function(){return _gc(_,_2E,_g0,_g6,_fS,_g3,_fT,_fU,_fZ,_fV,_fW,_fX,_fY);});}else{if(Math.sqrt(_g4*_g4+_g5*_g5)<=10){return new F(function(){return _gc(_,_2E,_g0,_g6,_fS,_g3,_fT,_fU,_fZ,_fV,_fW,_fX,_fY);});}else{return new F(function(){return _gc(_,_2E,new T(function(){var _jC=E(_fR[2]),_jD=Math.cos(_jC),_jE=Math.sin(_jC),_jF=Math.sqrt(_jD*_jD+_jE*_jE),_jG=_g3/20*((100-E(_fW))/300+1)/2/(Math.sqrt(E(_fU))/150+1)*E(_fY);return [0,_g1+_jD/_jF*_jG,_g2+_jE/_jF*_jG];}),_g6,_fS,_g3,_fT,_fU,_fZ,_fV,_fW,_fX,_fY);});}}};return E(_fN);default:return E(_fC);}})(_fz,_fA));if(_fB!=null){return _fB;}}},_jH=[1],_jI=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_jJ=function(_jK){return new F(function(){return err(_jI);});},_jL=new T(function(){return B(_jJ(_));}),_jM=function(_jN,_jO,_jP,_jQ){var _jR=E(_jQ);if(!_jR[0]){var _jS=_jR[1],_jT=E(_jP);if(!_jT[0]){var _jU=_jT[1],_jV=_jT[2],_jW=_jT[3];if(_jU<=(imul(3,_jS)|0)){return [0,(1+_jU|0)+_jS|0,E(_jN),_jO,E(_jT),E(_jR)];}else{var _jX=E(_jT[4]);if(!_jX[0]){var _jY=_jX[1],_jZ=E(_jT[5]);if(!_jZ[0]){var _k0=_jZ[1],_k1=_jZ[2],_k2=_jZ[3],_k3=_jZ[4];if(_k0>=(imul(2,_jY)|0)){var _k4=function(_k5){var _k6=E(_jZ[5]);return (_k6[0]==0)?[0,(1+_jU|0)+_jS|0,E(_k1),_k2,[0,(1+_jY|0)+_k5|0,E(_jV),_jW,E(_jX),E(_k3)],[0,(1+_jS|0)+_k6[1]|0,E(_jN),_jO,E(_k6),E(_jR)]]:[0,(1+_jU|0)+_jS|0,E(_k1),_k2,[0,(1+_jY|0)+_k5|0,E(_jV),_jW,E(_jX),E(_k3)],[0,1+_jS|0,E(_jN),_jO,E(_jH),E(_jR)]];},_k7=E(_k3);if(!_k7[0]){return new F(function(){return _k4(_k7[1]);});}else{return new F(function(){return _k4(0);});}}else{return [0,(1+_jU|0)+_jS|0,E(_jV),_jW,E(_jX),[0,(1+_jS|0)+_k0|0,E(_jN),_jO,E(_jZ),E(_jR)]];}}else{return E(_jL);}}else{return E(_jL);}}}else{return [0,1+_jS|0,E(_jN),_jO,E(_jH),E(_jR)];}}else{var _k8=E(_jP);if(!_k8[0]){var _k9=_k8[1],_ka=_k8[2],_kb=_k8[3],_kc=_k8[5],_kd=E(_k8[4]);if(!_kd[0]){var _ke=_kd[1],_kf=E(_kc);if(!_kf[0]){var _kg=_kf[1],_kh=_kf[2],_ki=_kf[3],_kj=_kf[4];if(_kg>=(imul(2,_ke)|0)){var _kk=function(_kl){var _km=E(_kf[5]);return (_km[0]==0)?[0,1+_k9|0,E(_kh),_ki,[0,(1+_ke|0)+_kl|0,E(_ka),_kb,E(_kd),E(_kj)],[0,1+_km[1]|0,E(_jN),_jO,E(_km),E(_jH)]]:[0,1+_k9|0,E(_kh),_ki,[0,(1+_ke|0)+_kl|0,E(_ka),_kb,E(_kd),E(_kj)],[0,1,E(_jN),_jO,E(_jH),E(_jH)]];},_kn=E(_kj);if(!_kn[0]){return new F(function(){return _kk(_kn[1]);});}else{return new F(function(){return _kk(0);});}}else{return [0,1+_k9|0,E(_ka),_kb,E(_kd),[0,1+_kg|0,E(_jN),_jO,E(_kf),E(_jH)]];}}else{return [0,3,E(_ka),_kb,E(_kd),[0,1,E(_jN),_jO,E(_jH),E(_jH)]];}}else{var _ko=E(_kc);return (_ko[0]==0)?[0,3,E(_ko[2]),_ko[3],[0,1,E(_ka),_kb,E(_jH),E(_jH)],[0,1,E(_jN),_jO,E(_jH),E(_jH)]]:[0,2,E(_jN),_jO,E(_k8),E(_jH)];}}else{return [0,1,E(_jN),_jO,E(_jH),E(_jH)];}}},_kp=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_kq=function(_kr){return new F(function(){return err(_kp);});},_ks=new T(function(){return B(_kq(_));}),_kt=function(_ku,_kv,_kw,_kx){var _ky=E(_kw);if(!_ky[0]){var _kz=_ky[1],_kA=E(_kx);if(!_kA[0]){var _kB=_kA[1],_kC=_kA[2],_kD=_kA[3];if(_kB<=(imul(3,_kz)|0)){return [0,(1+_kz|0)+_kB|0,E(_ku),_kv,E(_ky),E(_kA)];}else{var _kE=E(_kA[4]);if(!_kE[0]){var _kF=_kE[1],_kG=_kE[2],_kH=_kE[3],_kI=_kE[4],_kJ=E(_kA[5]);if(!_kJ[0]){var _kK=_kJ[1];if(_kF>=(imul(2,_kK)|0)){var _kL=function(_kM){var _kN=E(_ku),_kO=E(_kE[5]);return (_kO[0]==0)?[0,(1+_kz|0)+_kB|0,E(_kG),_kH,[0,(1+_kz|0)+_kM|0,E(_kN),_kv,E(_ky),E(_kI)],[0,(1+_kK|0)+_kO[1]|0,E(_kC),_kD,E(_kO),E(_kJ)]]:[0,(1+_kz|0)+_kB|0,E(_kG),_kH,[0,(1+_kz|0)+_kM|0,E(_kN),_kv,E(_ky),E(_kI)],[0,1+_kK|0,E(_kC),_kD,E(_jH),E(_kJ)]];},_kP=E(_kI);if(!_kP[0]){return new F(function(){return _kL(_kP[1]);});}else{return new F(function(){return _kL(0);});}}else{return [0,(1+_kz|0)+_kB|0,E(_kC),_kD,[0,(1+_kz|0)+_kF|0,E(_ku),_kv,E(_ky),E(_kE)],E(_kJ)];}}else{return E(_ks);}}else{return E(_ks);}}}else{return [0,1+_kz|0,E(_ku),_kv,E(_ky),E(_jH)];}}else{var _kQ=E(_kx);if(!_kQ[0]){var _kR=_kQ[1],_kS=_kQ[2],_kT=_kQ[3],_kU=_kQ[5],_kV=E(_kQ[4]);if(!_kV[0]){var _kW=_kV[1],_kX=_kV[2],_kY=_kV[3],_kZ=_kV[4],_l0=E(_kU);if(!_l0[0]){var _l1=_l0[1];if(_kW>=(imul(2,_l1)|0)){var _l2=function(_l3){var _l4=E(_ku),_l5=E(_kV[5]);return (_l5[0]==0)?[0,1+_kR|0,E(_kX),_kY,[0,1+_l3|0,E(_l4),_kv,E(_jH),E(_kZ)],[0,(1+_l1|0)+_l5[1]|0,E(_kS),_kT,E(_l5),E(_l0)]]:[0,1+_kR|0,E(_kX),_kY,[0,1+_l3|0,E(_l4),_kv,E(_jH),E(_kZ)],[0,1+_l1|0,E(_kS),_kT,E(_jH),E(_l0)]];},_l6=E(_kZ);if(!_l6[0]){return new F(function(){return _l2(_l6[1]);});}else{return new F(function(){return _l2(0);});}}else{return [0,1+_kR|0,E(_kS),_kT,[0,1+_kW|0,E(_ku),_kv,E(_jH),E(_kV)],E(_l0)];}}else{return [0,3,E(_kX),_kY,[0,1,E(_ku),_kv,E(_jH),E(_jH)],[0,1,E(_kS),_kT,E(_jH),E(_jH)]];}}else{var _l7=E(_kU);return (_l7[0]==0)?[0,3,E(_kS),_kT,[0,1,E(_ku),_kv,E(_jH),E(_jH)],E(_l7)]:[0,2,E(_ku),_kv,E(_jH),E(_kQ)];}}else{return [0,1,E(_ku),_kv,E(_jH),E(_jH)];}}},_l8=function(_l9,_la){var _lb=E(_la);if(!_lb[0]){var _lc=_lb[3],_ld=_lb[4],_le=_lb[5];switch(E(_lb[2])){case 0:return new F(function(){return _kt(_73,_lc,_ld,B(_l8(_l9,_le)));});break;case 1:return [0,_lb[1],E(_70),_l9,E(_ld),E(_le)];default:return new F(function(){return _jM(_6X,_lc,B(_l8(_l9,_ld)),_le);});}}else{return [0,1,E(_70),_l9,E(_jH),E(_jH)];}},_lf=function(_lg,_lh){var _li=E(_lh);if(!_li[0]){var _lj=_li[3],_lk=_li[4],_ll=_li[5];switch(E(_li[2])){case 0:return new F(function(){return _kt(_73,_lj,_lk,B(_lf(_lg,_ll)));});break;case 1:return new F(function(){return _kt(_70,_lj,_lk,B(_lf(_lg,_ll)));});break;default:return [0,_li[1],E(_6X),_lg,E(_lk),E(_ll)];}}else{return [0,1,E(_6X),_lg,E(_jH),E(_jH)];}},_lm=function(_ln,_lo){var _lp=E(_lo);if(!_lp[0]){var _lq=_lp[3],_lr=_lp[4],_ls=_lp[5];switch(E(_lp[2])){case 0:return [0,_lp[1],E(_73),_ln,E(_lr),E(_ls)];case 1:return new F(function(){return _jM(_70,_lq,B(_lm(_ln,_lr)),_ls);});break;default:return new F(function(){return _jM(_6X,_lq,B(_lm(_ln,_lr)),_ls);});}}else{return [0,1,E(_73),_ln,E(_jH),E(_jH)];}},_lt=function(_lu,_lv,_lw){var _lx=E(_lu),_ly=E(_lw);if(!_ly[0]){var _lz=_ly[1],_lA=_ly[2],_lB=_ly[3],_lC=_ly[4],_lD=_ly[5];switch(E(_lx)){case 0:switch(E(_lA)){case 0:return [0,_lz,E(_73),_lv,E(_lC),E(_lD)];case 1:return new F(function(){return _jM(_70,_lB,B(_lm(_lv,_lC)),_lD);});break;default:return new F(function(){return _jM(_6X,_lB,B(_lm(_lv,_lC)),_lD);});}break;case 1:switch(E(_lA)){case 0:return new F(function(){return _kt(_73,_lB,_lC,B(_l8(_lv,_lD)));});break;case 1:return [0,_lz,E(_70),_lv,E(_lC),E(_lD)];default:return new F(function(){return _jM(_6X,_lB,B(_l8(_lv,_lC)),_lD);});}break;default:switch(E(_lA)){case 0:return new F(function(){return _kt(_73,_lB,_lC,B(_lf(_lv,_lD)));});break;case 1:return new F(function(){return _kt(_70,_lB,_lC,B(_lf(_lv,_lD)));});break;default:return [0,_lz,E(_6X),_lv,E(_lC),E(_lD)];}}}else{return [0,1,E(_lx),_lv,E(_jH),E(_jH)];}},_lE=function(_lF,_lG){while(1){var _lH=E(_lG);if(!_lH[0]){return E(_lF);}else{var _lI=E(_lH[1]),_lJ=B(_lt(_lI[1],_lI[2],_lF));_lF=_lJ;_lG=_lH[2];continue;}}},_lK=function(_lL,_lM,_lN,_lO){return new F(function(){return _lE(B(_lt(_lM,_lN,_lL)),_lO);});},_lP=function(_lQ,_lR){return [0,1,E(_lQ),_lR,E(_jH),E(_jH)];},_lS=function(_lT,_lU,_lV){var _lW=E(_lV);if(!_lW[0]){return new F(function(){return _kt(_lW[2],_lW[3],_lW[4],B(_lS(_lT,_lU,_lW[5])));});}else{return new F(function(){return _lP(_lT,_lU);});}},_lX=function(_lY,_lZ,_m0){var _m1=E(_m0);if(!_m1[0]){return new F(function(){return _jM(_m1[2],_m1[3],B(_lX(_lY,_lZ,_m1[4])),_m1[5]);});}else{return new F(function(){return _lP(_lY,_lZ);});}},_m2=function(_m3,_m4,_m5,_m6,_m7,_m8,_m9){return new F(function(){return _jM(_m6,_m7,B(_lX(_m3,_m4,_m8)),_m9);});},_ma=function(_mb,_mc,_md,_me,_mf,_mg,_mh,_mi){var _mj=E(_md);if(!_mj[0]){var _mk=_mj[1],_ml=_mj[2],_mm=_mj[3],_mn=_mj[4],_mo=_mj[5];if((imul(3,_mk)|0)>=_me){if((imul(3,_me)|0)>=_mk){return [0,(_mk+_me|0)+1|0,E(_mb),_mc,E(_mj),[0,_me,E(_mf),_mg,E(_mh),E(_mi)]];}else{return new F(function(){return _kt(_ml,_mm,_mn,B(_ma(_mb,_mc,_mo,_me,_mf,_mg,_mh,_mi)));});}}else{return new F(function(){return _jM(_mf,_mg,B(_mp(_mb,_mc,_mk,_ml,_mm,_mn,_mo,_mh)),_mi);});}}else{return new F(function(){return _m2(_mb,_mc,_me,_mf,_mg,_mh,_mi);});}},_mp=function(_mq,_mr,_ms,_mt,_mu,_mv,_mw,_mx){var _my=E(_mx);if(!_my[0]){var _mz=_my[1],_mA=_my[2],_mB=_my[3],_mC=_my[4],_mD=_my[5];if((imul(3,_ms)|0)>=_mz){if((imul(3,_mz)|0)>=_ms){return [0,(_ms+_mz|0)+1|0,E(_mq),_mr,[0,_ms,E(_mt),_mu,E(_mv),E(_mw)],E(_my)];}else{return new F(function(){return _kt(_mt,_mu,_mv,B(_ma(_mq,_mr,_mw,_mz,_mA,_mB,_mC,_mD)));});}}else{return new F(function(){return _jM(_mA,_mB,B(_mp(_mq,_mr,_ms,_mt,_mu,_mv,_mw,_mC)),_mD);});}}else{return new F(function(){return _lS(_mq,_mr,[0,_ms,E(_mt),_mu,E(_mv),E(_mw)]);});}},_mE=function(_mF,_mG,_mH,_mI){var _mJ=E(_mH);if(!_mJ[0]){var _mK=_mJ[1],_mL=_mJ[2],_mM=_mJ[3],_mN=_mJ[4],_mO=_mJ[5],_mP=E(_mI);if(!_mP[0]){var _mQ=_mP[1],_mR=_mP[2],_mS=_mP[3],_mT=_mP[4],_mU=_mP[5];if((imul(3,_mK)|0)>=_mQ){if((imul(3,_mQ)|0)>=_mK){return [0,(_mK+_mQ|0)+1|0,E(_mF),_mG,E(_mJ),E(_mP)];}else{return new F(function(){return _kt(_mL,_mM,_mN,B(_ma(_mF,_mG,_mO,_mQ,_mR,_mS,_mT,_mU)));});}}else{return new F(function(){return _jM(_mR,_mS,B(_mp(_mF,_mG,_mK,_mL,_mM,_mN,_mO,_mT)),_mU);});}}else{return new F(function(){return _lS(_mF,_mG,_mJ);});}}else{return new F(function(){return _lX(_mF,_mG,_mI);});}},_mV=function(_mW,_mX,_mY,_mZ){var _n0=E(_mW);if(_n0==1){var _n1=E(_mZ);if(!_n1[0]){return [0,new T(function(){return [0,1,E(_mX),_mY,E(_jH),E(_jH)];}),_z,_z];}else{var _n2=E(_n1[1])[1];switch(E(_mX)){case 0:switch(E(_n2)){case 0:return [0,[0,1,E(_73),_mY,E(_jH),E(_jH)],_z,_n1];case 1:return [0,[0,1,E(_73),_mY,E(_jH),E(_jH)],_n1,_z];default:return [0,[0,1,E(_73),_mY,E(_jH),E(_jH)],_n1,_z];}break;case 1:return (E(_n2)==2)?[0,[0,1,E(_70),_mY,E(_jH),E(_jH)],_n1,_z]:[0,[0,1,E(_70),_mY,E(_jH),E(_jH)],_z,_n1];default:var _n3=E(_n2);return [0,[0,1,E(_6X),_mY,E(_jH),E(_jH)],_z,_n1];}}}else{var _n4=B(_mV(_n0>>1,_mX,_mY,_mZ)),_n5=_n4[1],_n6=_n4[3],_n7=E(_n4[2]);if(!_n7[0]){return [0,_n5,_z,_n6];}else{var _n8=E(_n7[1]),_n9=_n8[1],_na=_n8[2],_nb=E(_n7[2]);if(!_nb[0]){return [0,new T(function(){return B(_lS(_n9,_na,_n5));}),_z,_n6];}else{var _nc=_nb[2],_nd=E(_nb[1]),_ne=_nd[1],_nf=_nd[2];switch(E(_n9)){case 0:switch(E(_ne)){case 0:return [0,_n5,_z,_n7];case 1:var _ng=B(_mV(_n0>>1,_70,_nf,_nc));return [0,new T(function(){return B(_mE(_73,_na,_n5,_ng[1]));}),_ng[2],_ng[3]];default:var _nh=B(_mV(_n0>>1,_6X,_nf,_nc));return [0,new T(function(){return B(_mE(_73,_na,_n5,_nh[1]));}),_nh[2],_nh[3]];}break;case 1:if(E(_ne)==2){var _ni=B(_mV(_n0>>1,_6X,_nf,_nc));return [0,new T(function(){return B(_mE(_70,_na,_n5,_ni[1]));}),_ni[2],_ni[3]];}else{return [0,_n5,_z,_n7];}break;default:var _nj=E(_ne);return [0,_n5,_z,_n7];}}}}},_nk=function(_nl,_nm,_nn){var _no=E(_nm);return new F(function(){return _lE(B(_lt(_no[1],_no[2],_nl)),_nn);});},_np=function(_nq,_nr,_ns){var _nt=E(_ns);if(!_nt[0]){return E(_nr);}else{var _nu=E(_nt[1]),_nv=_nu[1],_nw=_nu[2],_nx=E(_nt[2]);if(!_nx[0]){return new F(function(){return _lS(_nv,_nw,_nr);});}else{var _ny=E(_nx[1]),_nz=_ny[1],_nA=function(_nB){var _nC=B(_mV(_nq,_nz,_ny[2],_nx[2])),_nD=_nC[1],_nE=E(_nC[3]);if(!_nE[0]){return new F(function(){return _np(_nq<<1,B(_mE(_nv,_nw,_nr,_nD)),_nC[2]);});}else{return new F(function(){return _nk(B(_mE(_nv,_nw,_nr,_nD)),_nE[1],_nE[2]);});}};switch(E(_nv)){case 0:switch(E(_nz)){case 0:return new F(function(){return _lK(_nr,_73,_nw,_nx);});break;case 1:return new F(function(){return _nA(_);});break;default:return new F(function(){return _nA(_);});}break;case 1:if(E(_nz)==2){return new F(function(){return _nA(_);});}else{return new F(function(){return _lK(_nr,_70,_nw,_nx);});}break;default:var _nF=E(_nz);return new F(function(){return _lK(_nr,_6X,_nw,_nx);});}}}},_nG=function(_nH){var _nI=E(_nH);if(!_nI[0]){return [1];}else{var _nJ=E(_nI[1]),_nK=_nJ[1],_nL=_nJ[2],_nM=E(_nI[2]);if(!_nM[0]){return [0,1,E(_nK),_nL,E(_jH),E(_jH)];}else{var _nN=_nM[2],_nO=E(_nM[1]),_nP=_nO[1],_nQ=_nO[2];switch(E(_nK)){case 0:switch(E(_nP)){case 0:return new F(function(){return _lK([0,1,E(_73),_nL,E(_jH),E(_jH)],_73,_nQ,_nN);});break;case 1:return new F(function(){return _np(1,[0,1,E(_73),_nL,E(_jH),E(_jH)],_nM);});break;default:return new F(function(){return _np(1,[0,1,E(_73),_nL,E(_jH),E(_jH)],_nM);});}break;case 1:var _nR=E(_nP);if(_nR==2){return new F(function(){return _np(1,[0,1,E(_70),_nL,E(_jH),E(_jH)],_nM);});}else{return new F(function(){return _lK([0,1,E(_70),_nL,E(_jH),E(_jH)],_nR,_nQ,_nN);});}break;default:return new F(function(){return _lK([0,1,E(_6X),_nL,E(_jH),E(_jH)],E(_nP),_nQ,_nN);});}}}},_nS=[1,_70,_eV],_nT=[1,_73,_nS],_nU=function(_nV,_nW){if(_nV<=_nW){var _nX=function(_nY){return [1,_nY,new T(function(){if(_nY!=_nW){return B(_nX(_nY+1|0));}else{return [0];}})];};return new F(function(){return _nX(_nV);});}else{return [0];}},_nZ=new T(function(){return B(_nU(0,2147483647));}),_o0=function(_o1,_o2){var _o3=E(_o1);if(!_o3[0]){return [0];}else{var _o4=E(_o2);return (_o4[0]==0)?[0]:[1,[0,_o3[1],_o4[1]],new T(function(){return B(_o0(_o3[2],_o4[2]));})];}},_o5=new T(function(){return B(_o0(_nT,_nZ));}),_o6=new T(function(){return B(_nG(_o5));}),_o7=new T(function(){return B(unCStr("Pattern match failure in do expression at src/main.hs:316:3-9"));}),_o8=[0,_2e,_2f,_z,_o7,_2e,_2e],_o9=new T(function(){return B(_2c(_o8));}),_oa=[1,30],_ob="game-stop",_oc="game-run",_od=[2],_oe=[0,E(_od),_2e,_z,_4n,_74],_of=new T(function(){return B(unCStr("img/creature0.png"));}),_og=new T(function(){return B(unCStr("img/creature1.png"));}),_oh=new T(function(){return B(unCStr("img/creature2.png"));}),_oi=[1,_oh,_z],_oj=[1,_og,_oi],_ok=function(_ol){return E(E(_ol)[1]);},_om=function(_on){return E(E(_on)[1]);},_oo=function(_op){return E(E(_op)[1]);},_oq=function(_or){return E(E(_or)[2]);},_os=function(_ot){return E(E(_ot)[1]);},_ou=function(_){return new F(function(){return nMV(_2e);});},_ov=new T(function(){return B(_2r(_ou));}),_ow=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_ox=function(_oy){return E(E(_oy)[2]);},_oz=function(_oA,_oB,_oC,_oD,_oE,_oF){var _oG=B(_ok(_oA)),_oH=B(_om(_oG)),_oI=new T(function(){return B(_2w(_oG));}),_oJ=new T(function(){return B(_a1(_oH));}),_oK=new T(function(){return B(A(_oo,[_oB,_oD]));}),_oL=new T(function(){return B(A(_os,[_oC,_oE]));}),_oM=function(_oN){return new F(function(){return A(_oJ,[[0,_oL,_oK,_oN]]);});},_oO=function(_oP){var _oQ=new T(function(){var _oR=new T(function(){var _oS=__createJSFunc(2,function(_oT,_){var _oU=B(A(E(_oP),[_oT,_]));return _2v;}),_oV=_oS;return function(_){return new F(function(){return E(_ow)(E(_oK),E(_oL),_oV);});};});return B(A(_oI,[_oR]));});return new F(function(){return A(_9J,[_oH,_oQ,_oM]);});},_oW=new T(function(){var _oX=new T(function(){return B(_2w(_oG));}),_oY=function(_oZ){var _p0=new T(function(){return B(A(_oX,[function(_){var _=wMV(E(_ov),[1,_oZ]);return new F(function(){return A(_oq,[_oC,_oE,_oZ,_]);});}]));});return new F(function(){return A(_9J,[_oH,_p0,_oF]);});};return B(A(_ox,[_oA,_oY]));});return new F(function(){return A(_9J,[_oH,_oW,_oO]);});},_p1=(function(t,f){window.setInterval(f,t);}),_p2=(function(t,f){window.setTimeout(f,t);}),_p3=function(_p4,_p5,_p6){var _p7=B(_ok(_p4)),_p8=new T(function(){return B(_2w(_p7));}),_p9=function(_pa){var _pb=function(_){var _pc=E(_p5);if(!_pc[0]){var _pd=B(A(_pa,[_2E])),_pe=__createJSFunc(0,function(_){var _pf=B(A(_pd,[_]));return _2v;}),_pg=E(_p2)(_pc[1],_pe);return new T(function(){var _ph=Number(_pg),_pi=jsTrunc(_ph);return [0,_pi,E(_pc)];});}else{var _pj=B(A(_pa,[_2E])),_pk=__createJSFunc(0,function(_){var _pl=B(A(_pj,[_]));return _2v;}),_pm=E(_p1)(_pc[1],_pk);return new T(function(){var _pn=Number(_pm),_po=jsTrunc(_pn);return [0,_po,E(_pc)];});}};return new F(function(){return A(_p8,[_pb]);});},_pp=new T(function(){return B(A(_ox,[_p4,function(_pq){return E(_p6);}]));});return new F(function(){return A(_9J,[B(_om(_p7)),_pp,_p9]);});},_pr=[0,E(_eU),E(_eT)],_ps=new T(function(){return B(unCStr(" found!"));}),_pt=function(_pu){return new F(function(){return err(B(unAppCStr("No element with ID ",new T(function(){return B(_V(fromJSStr(E(_pu)),_ps));}))));});},_pv=function(_pw,_px,_py){var _pz=new T(function(){var _pA=function(_){var _pB=E(_2p)(E(_px)),_pC=__eq(_pB,E(_2v));return (E(_pC)==0)?[1,_pB]:_2e;};return B(A(_2w,[_pw,_pA]));});return new F(function(){return A(_9J,[B(_om(_pw)),_pz,function(_pD){var _pE=E(_pD);if(!_pE[0]){return new F(function(){return _pt(_px);});}else{return new F(function(){return A(_py,[_pE[1]]);});}}]);});},_pF=function(_,_pG){var _pH=E(_pG);if(!_pH[0]){return new F(function(){return die(_o9);});}else{var _pI=B(_4V(_of,_oj,_)),_pJ=_pI,_pK=function(_pL,_pM){while(1){var _pN=B((function(_pO,_pP){var _pQ=E(_pP);switch(_pQ[0]){case 0:_pL=new T(function(){return B(_pK(_pO,_pQ[4]));});_pM=_pQ[3];return null;case 1:var _pR=_pQ[2],_pS=new T(function(){return B(_5e(_pJ,B(_4A(E(_pR)[5],_o6))));});return function(_pT,_){var _pU=E(E(_pR)[1]),_pV=E(_pT),_pW=B(_6z(E(_pS),E(_pU[1]),E(_pU[2]),_pV,_));return new F(function(){return A(_pO,[_pV,_]);});};default:return E(_pO);}})(_pL,_pM));if(_pN!=null){return _pN;}}},_pX=function(_pY,_){var _pZ=E(_pY);if(!_pZ[0]){var _q0=nMV(_oe),_q1=_q0,_q2=function(_){var _q3=rMV(_q1),_q4=E(_bb)(),_q5=E(_q3),_q6=_q5[1],_q7=_q5[2],_q8=_q5[3],_q9=_q5[4],_qa=_q5[5],_qb=new T(function(){return E(B(_6j(_fl,_pr,_q4))[1]);});if(B(_6F(B(_82(_q6)),0))>=1000){var _=wMV(_q1,[0,E(_q6),_q7,_q8,_q9,_qa]);return _2E;}else{var _=wMV(_q1,[0,E(B(_7R([0,_qb,_75,_7e,_7a,_73,_4n,_qb,_71,_77,_76,_76],_q6))),_q7,_q8,_q9,_qa]);return _2E;}},_qc=function(_qd,_){while(1){var _qe=E(_qd);if(_qe==1){var _qf=B(_q2(_));return _2E;}else{var _qg=B(_q2(_));_qd=_qe-1|0;continue;}}},_qh=B(_qc(50,_)),_qi=function(_){var _qj=rMV(_q1),_qk=E(_bb)(),_ql=E(_qj),_qm=_ql[1],_qn=_ql[2],_qo=_ql[3],_qp=_ql[4],_qq=_ql[5],_qr=new T(function(){return E(B(_6j(_fl,_pr,_qk))[1]);});if(B(_6L(B(_82(_qm)),0))>=200){var _=wMV(_q1,[0,E(_qm),_qn,_qo,_qp,_qq]);return _2E;}else{var _=wMV(_q1,[0,E(B(_7R([0,_qr,_75,_7d,_7c,_70,_4n,_qr,_71,_77,_76,_76],_qm))),_qn,_qo,_qp,_qq]);return _2E;}},_qs=function(_qt,_){while(1){var _qu=E(_qt);if(_qu==1){var _qv=B(_qi(_));return _2E;}else{var _qw=B(_qi(_));_qt=_qu-1|0;continue;}}},_qx=B(_qs(20,_)),_qy=function(_){var _qz=rMV(_q1),_qA=E(_bb)(),_qB=E(_qz),_qC=_qB[1],_qD=_qB[2],_qE=_qB[3],_qF=_qB[4],_qG=_qB[5],_qH=new T(function(){return E(B(_6j(_fl,_pr,_qA))[1]);});if(B(_6R(B(_82(_qC)),0))>=50){var _=wMV(_q1,[0,E(_qC),_qD,_qE,_qF,_qG]);return _2E;}else{var _=wMV(_q1,[0,E(B(_7R([0,_qH,_75,_7b,_7c,_6X,_4n,_qH,_71,_77,_76,_76],_qC))),_qD,_qE,_qF,_qG]);return _2E;}},_qI=function(_qJ,_){while(1){var _qK=E(_qJ);if(_qK==1){var _qL=B(_qy(_));return _2E;}else{var _qM=B(_qy(_));_qJ=_qK-1|0;continue;}}},_qN=B(_qI(3,_)),_qO=function(_){var _qP=rMV(_q1),_qQ=E(_qP),_=wMV(_q1,[0,E(_qQ[1]),_qQ[2],_qQ[3],_qQ[4],_74]);return _2E;},_qR=function(_qS,_){return new F(function(){return _qO(_);});},_qT=B(A(_pv,[_2o,_oc,function(_qU){return new F(function(){return _oz(_4m,_4l,_4i,_qU,_6Y,_qR);});},_])),_qV=function(_){var _qW=rMV(_q1),_qX=E(_qW),_=wMV(_q1,[0,E(_qX[1]),_qX[2],_qX[3],_qX[4],_6Z]);return _2E;},_qY=function(_qZ,_){return new F(function(){return _qV(_);});},_r0=B(A(_pv,[_2o,_ob,function(_r1){return new F(function(){return _oz(_4m,_4l,_4i,_r1,_6Y,_qY);});},_])),_r2=function(_){var _r3=rMV(_q1),_r4=E(_r3),_r5=_r4[1];if(!E(_r4[5])){var _=wMV(_q1,_r4);return _2E;}else{var _r6=function(_,_r7){var _r8=E(_pH[1]),_r9=_r8[1],_ra=E(_7f)(_r8[2]),_rb=E(_r5);if(!_rb[0]){var _rc=_rb[3],_rd=_rb[4];if(_rb[2]>=0){var _re=B(A(_pK,[new T(function(){return B(_pK(_78,_rd));}),_rc,_r9,_])),_=wMV(_q1,E(E(_r7)[2]));return _2E;}else{var _rf=B(A(_pK,[new T(function(){return B(_pK(_78,_rc));}),_rd,_r9,_])),_=wMV(_q1,E(E(_r7)[2]));return _2E;}}else{var _rg=B(A(_pK,[_78,_rb,_r9,_])),_=wMV(_q1,E(E(_r7)[2]));return _2E;}},_rh=E(_r5);if(!_rh[0]){var _ri=_rh[3],_rj=_rh[4];if(_rh[2]>=0){var _rk=B(A(_fy,[new T(function(){return B(_fy(_50,_rj));}),_ri,_r4,_]));return new F(function(){return _r6(_,_rk);});}else{var _rl=B(A(_fy,[new T(function(){return B(_fy(_50,_ri));}),_rj,_r4,_]));return new F(function(){return _r6(_,_rl);});}}else{var _rm=B(A(_fy,[_50,_rh,_r4,_]));return new F(function(){return _r6(_,_rm);});}}},_rn=B(A(_p3,[_4m,_oa,_r2,_]));return _2E;}else{var _ro=B(A(_oz,[_4m,_4l,_2S,_pZ[1],_72,function(_rp,_){return new F(function(){return _pX(_pZ[2],_);});},_]));return _2E;}};return new F(function(){return _pX(_pJ,_);});}},_rq="hakoniwa-canvas",_rr=function(_){var _rs=B(A(_2y,[_2o,_rq,_])),_rt=E(_rs);if(!_rt[0]){return new F(function(){return _pF(_,_2e);});}else{var _ru=E(_rt[1]),_rv=E(_1)(_ru);if(!_rv){return new F(function(){return _pF(_,_2e);});}else{var _rw=E(_0)(_ru);return new F(function(){return _pF(_,[1,[0,_rw,_ru]]);});}}},_rx=function(_){return new F(function(){return _rr(_);});};
var hasteMain = function() {B(A(_rx, [0]));};window.onload = hasteMain;