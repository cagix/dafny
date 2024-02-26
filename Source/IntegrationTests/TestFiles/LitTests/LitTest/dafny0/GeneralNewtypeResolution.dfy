// RUN: %exits-with 2 %dafny /typeSystemRefresh:1 /generalTraits:datatype /generalNewtypes:0 "%s" > "%t"
// RUN: %exits-with 2 %dafny /typeSystemRefresh:1 /generalTraits:datatype /generalNewtypes:1 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module VariousBaseTypes {
  newtype byteA = x | 0 <= x < 256

  newtype byteB = x: int | 0 <= x < 256

  newtype MyInt = int

  // cycle one way
  newtype A = B
  newtype B = c: C | true witness *
  newtype C = d | d < 100

  // cycle the other way
  newtype Z = d | d < 100
  newtype Y = c: Z | true witness *
  newtype X = Y

  newtype MyReal0 = real
  newtype MyReal1 = r | 0.0 <= r <= 100.0
  newtype MyReal2 = r: real | 0.0 <= r <= 100.0

  // The following are allowed with /generalNewtypes:1, but errors with /generalNewtypes:0

  newtype NotNumeric0 = bool // error: cannot base newtype on bool
  newtype NotNumeric1 = b | !b // error: cannot base newtype on bool
  newtype NotNumeric2 = b: bool | true // error: cannot base newtype on bool

  // The following are always errors

  newtype MyOrdinal = ORDINAL // error: cannot base newtype on ORDINAL

  trait Trait { }
  trait ReferenceTrait extends object { }
  class Cell { }

  newtype MyObject = object // error: cannot base newtype on (reference) trait
  newtype MyTrait = Trait // error: cannot base newtype on (non-reference) trait
  newtype MyReferenceTrait = ReferenceTrait // error: cannot base newtype on (reference) trait
  newtype MyCell? = Cell? // error: cannot base newtype on class
  newtype MyCell = Cell // error: cannot base newtype on class
}

module BaseTypesThatAreSubsetTypes {
  newtype byteB = x: nat | x < 256

  newtype MyNat = nat

  // cycle one way
  newtype A = B
  newtype B = c: C | true witness *
  newtype C = d: nat | d < 100

  // cycle the other way
  newtype Z = d: nat | d < 100
  newtype Y = c: Z | true witness *
  newtype X = Y

  type NonNegReal = r | 0.0 <= r
  newtype MyReal = NonNegReal
  newtype MyReal' = r: NonNegReal | r <= 100.0

  // The following are allowed with /generalNewtypes:1, but errors with /generalNewtypes:0

  type True = b | !!b
  newtype NotNumeric = True // error: cannot base newtype on bool
  newtype NotNumeric' = b: True | true // error: cannot base newtype on bool

  // The following are always errors

  type NonFiveOrdinal = o: ORDINAL | o != 5
  newtype MyOrdinal = NonFiveOrdinal // error: cannot base newtype on ORDINAL

  trait Trait { const n: int }
  type NonFiveTrait = t: Trait | t.n != 5
  trait ReferenceTrait extends object { const n: int }
  type NonFiveReferenceTrait = t: ReferenceTrait | t.n != 5
  class Cell { const n: int }
  type NonFiveCell? = t: Cell? | t == null || t.n != 5
  type NonFiveCell = t: Cell | t.n != 5

  newtype MyTrait = NonFiveTrait // error: cannot base newtype on (non-reference) trait
  newtype MyReferenceTrait = NonFiveReferenceTrait // error: cannot base newtype on (reference) trait
  newtype MyCell? = NonFiveCell? // error: cannot base newtype on class
  newtype MyCell = NonFiveCell // error: cannot base newtype on class
}

module SomeOperators {
  newtype TrueBool = b | b witness true
  newtype FalseBool = b | !b
  codatatype Stream = More(Stream)

  method Comparisons(x: TrueBool, y: FalseBool, z: bool, s: Stream, k: nat, o: ORDINAL) returns (r: TrueBool, r': FalseBool) {
    r := x == x;
    r := y == y;
    r := z == z;
    r := s ==#[k] s;
    r := s ==#[o] s;
    r := k == k;
    r := o == o;

    r := x <==> x;
    r := y <==> y; // error: <==> always results in the same type as its operands
    r := z <==> z; // error: <==> always results in the same type as its operands

    r := x ==> x;
    r := y ==> y; // error: ==> always results in the same type as its operands
    r := z ==> z; // error: ==> always results in the same type as its operands

    r := x <== x;
    r := y <== y; // error: <== always results in the same type as its operands
    r := z <== z; // error: <== always results in the same type as its operands

    r := x && x;
    r := y && y; // error: && always results in the same type as its operands
    r := z && z; // error: && always results in the same type as its operands

    r := x || x;
    r := y || y; // error: || always results in the same type as its operands
    r := z || z; // error: || always results in the same type as its operands

    r := k <= k;
    r := k >= k;
    r' := k < k;
    r' := k > k;
  }
}

module WhatCanBeCompiled {
  newtype MyBool = bool
  newtype AnyBool = b: bool | true
  newtype TrueBool = b | b

  function Exp(x: int, n: nat): int {
    if n == 0 then 1 else x * Exp(x, n - 1)
  }
  newtype FermatBool = b | b <==>
    forall x, y, z, n: nat :: 1 <= x && 1 <= y && 1 <= z && Exp(x, n) + Exp(y, n) == Exp(z, n) ==> n <= 2
    witness *

  ghost predicate G(b: bool) { b }
  newtype GhostBool = b | G(b)

  newtype OnTopOfGhostBool = g: GhostBool | true witness false

  method AsTest(b: bool) {
    if
    case true =>
      var m: MyBool;
      m := b as MyBool;
    case true =>
      var a: AnyBool;
      a := b as AnyBool;
    case true =>
      var t: TrueBool;
      t := b as TrueBool;
    case true =>
      var f: FermatBool;
      f := b as FermatBool;
    case true =>
      var g: GhostBool;
      g := b as GhostBool;
    case true =>
      var o: OnTopOfGhostBool;
      o := b as OnTopOfGhostBool;
  }

  method IsTest(b: bool) returns (r: bool) {
    if
    case true =>
      r := b is MyBool;
    case true =>
      r := b is AnyBool;
    case true =>
      r := b is TrueBool;
    case true =>
      r := b is FermatBool; // error: this type test is ghost
    case true =>
      r := b is GhostBool; // error: this type test is ghost
    case true =>
      r := b is OnTopOfGhostBool; // error: this type test is ghost
  }
}

module DiscoverBounds {
  newtype TrueAsCanBe = b: bool | b witness true

  method Test(s: set<TrueAsCanBe>) {
    assert forall x :: x in s ==> x == true;
  }
}

module Char {
  newtype MyChar = char
  newtype UpperCase = ch | 'A' <= ch <= 'Z' witness 'D'

  method Comparisons() returns (c: MyChar, u: UpperCase, r: bool) {
    c := 'e';
    u := 'E';

    r := c == c;
    r := u != u;
    r := c == u; // error: types don't match

    r := c < c;
    r := c <= c;
    r := c >= c;
    r := c > c;

    r := u <= u <= u;
    r := u < c; // error: types don't match
    r := u <= c; // error: types don't match
    r := u >= c; // error: types don't match
    r := u > c; // error: types don't match

    if c == 'f' && u == 'D' {
      r := true;
    }
  }

  method PlusMinus(c: MyChar, u: UpperCase, ch: char) {
    var d := c - c + c;
    var v := u - 'A' + 'd';

    var e0 := c + u; // error: types don't match
    var e1 := ch + c; // error: types don't match

    var d := c as char - c as char + c as char;
    var A: char := 'A';
    var v := u - A as UpperCase + 'd' as MyChar as UpperCase;

    var x: int;
    x := ch as int;
    x := c as char as int;
    x := u as char as int;
    x := c as int; // error: cannot go directly from char-newtype to int
    x := u as int; // error: cannot go directly from char-newtype to int
  }
}

module BitvectorOperators {
  newtype BV = b: bv17 | b != 123
  newtype Word = bv32
  newtype Big = b: bv1024 | true
  newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

  method Comparisons(x: BV, y: Word, z: Big, a: bv17, b: bv32, c: bv1024, i: int, j: int32) returns (r: bool, s: BV) {
    r := x == x;
    r := y == y;
    r := z == z;

    r := x == 5;
    r := x == y; // error: type mismatch
    r := x == a; // error: type mismatch
    r := x == b; // error: type mismatch
    r := x == i; // error: type mismatch
    r := x == j; // error: type mismatch

    // + - * / %
    s := x + x - x * (x + x / x - x % x);
    s := 12 + x - x * (x + 19 / 17 - x % 3);
    s := 12 + 13 - 14 * (15 + 16 / 17 - 18 % 19);
    s := x + y; // error: type mismatch
    s := x - z; // error: type mismatch
    s := x * a; // error: type mismatch
    s := x / b; // error: type mismatch
    s := x % c; // error: type mismatch

    // & | ^
    s := (x & x) | (x ^ x ^ x);
    s := (12 & 13) | (14 ^ 15 ^ 16);
    s := a & x; // error: type mismatch
    s := b | x; // error: type mismatch
    s := z ^ x; // error: type mismatch

    // << >>
    s := x << x << 3 << y << i << j;
    s := x >> x >> 3 >> y >> i >> j;
    s := b << x << 3; // error: RHS type not assignable to LHS
    s := b >> x >> 3; // error: RHS type not assignable to LHS

    //  .RotateLeft .RotateRight
    s := x.RotateLeft(3).RotateRight(j); // error: argument type expected to be nat
    s := x.RotateRight(j); // error: argument type expected to be nat
    s := x.RotateLeft(3 as int).RotateRight(j as nat);
    s := b.RotateLeft(x as nat).RotateRight(i as int); // error: RHS type not assignable to LHS type

    // < <= >= >
    r := (x <= x && x < x) || x >= x || x > x;
    r := x < a; // error: type mismatch
    r := x <= b; // error: type mismatch
    r := x >= c; // error: type mismatch
    r := x > z; // error: type mismatch
  }

  method Conversions() returns (x: BV, y: Word, z: Big, a: bv17, b: bv32, c: bv1024, i: int, j: int32, r: bool) {
    x := 10;
    x := x;
    x := y; // error: type mismatch
    x := z; // error: type mismatch
    x := a; // error: type mismatch
    x := b; // error: type mismatch
    x := c; // error: type mismatch
    x := i; // error: type mismatch
    x := j; // error: type mismatch
  
    x := 10 as BV; // (the "10" gets type "int" by way of advice)
    x := x as BV;
    x := y as BV;
    x := z as BV;
    x := a as BV;
    x := b as BV;
    x := c as BV;
    x := i as BV;
    x := j as BV;

    r := 10 is BV; // (the "10" gets type "int" by way of advice)
    r := x is BV;
    r := y is BV;
    r := z is BV;
    r := a is BV;
    r := b is BV;
    r := c is BV;
    r := i is BV;
    r := j is BV;

    r := 10 is bv17; // (the "10" gets type "int" by way of advice)
    r := x is bv17;
    r := y is bv17;
    r := z is bv17;
    r := a is bv17;
    r := b is bv17;
    r := c is bv17;
    r := i is bv17;
    r := j is bv17;
  }
}

module BitvectorForRuntimeChecks0 {
  newtype BV = b: bv17 | b != 123
  newtype Word = bv32
  newtype Big = b: bv1024 | true
  newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

  method Comparisons(x: BV, y: Word, z: Big, a: bv17, b: bv32, c: bv1024, i: int, j: int32) returns (r: bool, s: BV) {
    r := x == x;
    r := y == y;
    r := z == z;

    r := x == 5;

    // + - * / %
    s := x + x - x * (x + x / x - x % x);
    s := 12 + x - x * (x + 19 / 17 - x % 3);
    s := 12 + 13 - 14 * (15 + 16 / 17 - 18 % 19);

    // & | ^
    s := (x & x) | (x ^ x ^ x);
    s := (12 & 13) | (14 ^ 15 ^ 16);

    // << >>
    s := x << x << 3 << y << i << j;
    s := x >> x >> 3 >> y >> i >> j;

    //  .RotateLeft .RotateRight
    s := x.RotateLeft(3) as BV;
    s := x.RotateRight(j as nat) as BV;

    // < <= >= >
    r := (x <= x && x < x) || x >= x || x > x;
  }

  method Conversions() returns (x: BV, y: Word, z: Big, a: bv17, b: bv32, c: bv1024, i: int, j: int32, r: bool) {
    r := 10 is BV;
    r := 10 is Word;
    r := x is Word;
    r := y is Word;

    r := 10 is bv17;
    r := x is bv17;
    r := y is bv17;
    r := z is bv17;
    r := a is bv17;
    r := b is bv17;
    r := c is bv17;
    r := i is bv17;
    r := j is bv17;
  }
}

module BitvectorForRuntimeChecks1 {
  newtype BV = b: bv17 | b != 123
  newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

  method RotateL(x: BV, j: int32) returns (s: BV) {
    s := x.RotateLeft(3); // error: RotateLeft/RotateRight always return the plain bv type (here, bv17)
  }

  method RotateR(x: BV, j: int32) returns (s: BV) {
    s := x.RotateRight(j as nat); // error: RotateLeft/RotateRight always return the plain bv type (here, bv17)
  }
}

module BitvectorForRuntimeChecks2 {
  newtype BV = b: bv17 | b != 123
  newtype Word = bv32

  newtype GhostBits = b: bv109 | GhostPredicate(b)

  ghost predicate GhostPredicate(x: bv109) {
    true
  }

  method Comprehensions(aa: set<bv7>, bb: set<BV>, cc: set<Word>, dd: set<GhostBits>) {
    var se0, se1, se2, se3;
    se0 := set x | x in aa;
    se1 := set x | x in bb;
    se2 := set x | x in cc;
    se3 := set x | x in dd; // error: GhostBits is not compilable
  }
}

module BitvectorCharConversion {
  type Char = ch: char | true

  method Test() returns (c: char, d: Char, a: bv5) {
    if
    case true =>
      d := c as Char;
    case true =>
      d := a as Char; // error -- this conversion is allowed only under /generalNewtypes:0
    case true =>
      d := (a as int) as Char;
  }
}

module NativeTypePreference {
  newtype {:nativeType "int"} RR = x: real | 0.0 <= x <= 3.0 // error: not integer or bitvector type
//SOON:  newtype {:nativeType "int"} TT = x: (int, int) | x.0 == x.1 // error: not integer or bitvector type
  newtype {:nativeType "uint"} BB0 = x: bv325 | 0 <= x < 300 // error (with hint): does not fit into bv325
  newtype {:nativeType "uint"} BB1 = bv325 // error: does not fit into bv325

  newtype {:nativeType "long"} C0 = x: int | 0 <= x < 280 witness 23
  type C1 = x: C0 | x != 199 witness 24
  newtype {:nativeType "short"} C2 = C1
  newtype C3 = x: C2 | x % 2 == 0 witness 28
  newtype {:nativeType "byte"} C4 = x: C3 | x < 100 witness 30

  newtype {:nativeType "long"} ZZ0 = x: bv0 | true // error (with hint): cannot use native type that admits negative values
  newtype {:nativeType "ulong"} ZZ1 = x: bv0 | true
  newtype {:nativeType "number"} ZZ2 = x: bv0 | true // error: cannot use native type that admits negative values

  newtype {:nativeType "short"} WW0 = bv7 // error (with hint): cannot use native type that admits negative values
  newtype {:nativeType "ushort"} WW1 = bv7
  newtype {:nativeType "number"} WW2 = x: bv7 | true // error: cannot use native type that admits negative values

  newtype {:nativeType "ulong"} D0 = x: bv13 | 0 <= x < 280 witness 23
  type D1 = x: D0 | x != 199 witness 24
  newtype {:nativeType "ushort"} D2 = D1
  newtype D3 = x: D2 | x % 2 == 0 witness 28
  // A newtype based on a bitvector is always native-sized according to the bitvector width, regardless of any constraints. Hence,
  // there is an error reported on the next line.
  newtype {:nativeType "byte"} D4 = x: D3 | x < 100 witness 30 // error: "byte" cannot be determined to be big enough
}

module CyclesInFiguringOutWhatIsCompilable {
  type OnTopOfNat = n: nat | true

  predicate P(x: int) { true }
  type PUp = x: int | P(x) // compilable, since P is
  type PPUp = s: set<int> | |set x: PUp | x in s| < 10 // compilable, since PUp is

  type PPDown = s: set<int> | |set x: PDown | x in s| < 10 // compilable, since PDown is
  type PDown = x: int | P(x) // compilable, since P is

  type PSpiral4 = x: PSpiral3 | true
  type PSpiral2 = x: PSpiral1 | true
  type PSpiral0 = x: int | P(x)
  type PSpiral1 = x: PSpiral0 | true
  type PSpiral3 = x: PSpiral2 | true

  method AllFine(x: int, s: set<int>) {
    print x is OnTopOfNat;
    print x is PUp;
    print x is PDown;
    print s is PPUp;
    print s is PPDown;
    print x is PSpiral0;
    print x is PSpiral1;
    print x is PSpiral2;
    print x is PSpiral3;
    print x is PSpiral4;
  }


  ghost predicate Q(x: int) { true }
  type QUp = x: int | Q(x) // not compilable, since Q isn't
  type QQUp = s: set<int> | |set x: QUp | x in s| < 10 // not compilable, since QUp isn't
  type QQDown = s: set<int> | |set x: QDown | x in s| < 10 // not compilable, since QDown isn't
  type QDown = x: int | Q(x) // not compilable, since Q isn't

  type QSpiral4 = x: QSpiral3 | true
  type QSpiral2 = x: QSpiral1 | true
  type QSpiral0 = x: int | Q(x)
  type QSpiral1 = x: QSpiral0 | true
  type QSpiral3 = x: QSpiral2 | true

  method Errors(x: int, s: set<int>) {
    print x is QUp; // error: not compilable
    print x is QDown; // error: not compilable
    print s is QQUp; // error: not compilable
    print s is QQDown; // error: not compilable
    print x is QSpiral0; // error: not compilable
    print x is QSpiral1; // error: not compilable
    print x is QSpiral2; // error: not compilable
    print x is QSpiral3; // error: not compilable
    print x is QSpiral4; // error: not compilable
  }
}

module ForallStatementRegression {
  ghost predicate P(x: int) {
    x != 11
  }

  newtype MyInt = x: int | -2 <= x < 16 && P(x)

  method Test() {
    var a := new int[20];
    forall i: MyInt | 5 <= i && i as int < a.Length { // error: not compilable (since P is ghost)
      a[i] := i as int;
    }
    print a[..], "\n";
  }
}
