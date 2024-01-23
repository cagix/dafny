// RUN: %baredafny translate rs %args "%s"
// RUN: %baredafny run --target=rs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
const TWO_TO_THE_8:   int := 0x100
const TWO_TO_THE_16:  int := 0x10000
const TWO_TO_THE_32:  int := 0x1_00000000
const TWO_TO_THE_64:  int := 0x1_00000000_00000000
newtype uint8  = x: int | 0 <= x < TWO_TO_THE_8
newtype uint16 = x: int | 0 <= x < TWO_TO_THE_16
newtype uint32 = x: int | 0 <= x < TWO_TO_THE_32
newtype uint64 = x: int | 0 <= x < TWO_TO_THE_64

newtype int8  = x: int  | -0x80 <= x < 0x80
newtype int16 = x: int  | -0x8000 <= x < 0x8000
newtype int32 = x: int  | -0x8000_0000 <= x < 0x8000_0000
newtype int64 = x: int  | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

method Main() {
  var t := true;
  var f := false;
  if ((t && f) || f) ==> f {
    print "&& || ==> ";
  }
  if t && f <==> f && t {
    print "<==> ";
  }

  if 2 <= 3 && 2 < 3 && 3 >= 2 && 3 > 2 && 3 != 2 && 2 == 2 {
    print "<= < >= > != == ";
  }

  var o8: uint8 := 1 as uint8;
  var s8: uint8 := 2 as uint8;
  var w8: uint8 := 5 as uint8;
  var x8: uint8 := 8 as uint8;
  var y8: uint8 := 13 as uint8;
  var z8: uint8 := 21 as uint8;
  var m8: uint8 := 24 as uint8;
  var t8: uint8 := 16 as uint8;
  if x8 + y8 == z8
     && y8 - x8 == z8
     && x8 as bv8 & y8 as bv8 == x8 as bv8
     && x8 as bv8 | y8 as bv8 == y8 as bv8
     && x8 as bv8 ^ y8 as bv8 == w8 as bv8
     && x8 * 3 == m8
     && x8 as bv8 >> s8 == s8 as bv8
     && x8 as bv8 << o8 == t8 as bv8 {
    print "operators(u8) ";
  }

  
  var o16: uint16 := 1 as uint16;
  var s16: uint16 := 2 as uint16;
  var w16: uint16 := 5 as uint16;
  var x16: uint16 := 8 as uint16;
  var y16: uint16 := 13 as uint16;
  var z16: uint16 := 21 as uint16;
  var m16: uint16 := 24 as uint16;
  var t16: uint16 := 16 as uint16;
  if x16 + y16 == z16
     && y16 - x16 == z16
     && x16 as bv16 & y16 as bv16 == x16 as bv16
     && x16 as bv16 | y16 as bv16 == y16 as bv16
     && x16 as bv16 ^ y16 as bv16 == w16 as bv16
     && x16 * 3 == m16
     && x16 as bv16 >> s16 as bv16 == s16 as bv16
     && x16 as bv16 << o16 as bv16 == t16 as bv16 {
    print "operators(u16) ";
  }
  
  var o32: uint32 := 1 as uint32;
  var s32: uint32 := 2 as uint32;
  var w32: uint32 := 5 as uint32;
  var x32: uint32 := 8 as uint32;
  var y32: uint32 := 13 as uint32;
  var z32: uint32 := 21 as uint32;
  var m32: uint32 := 24 as uint32;
  var t32: uint32 := 16 as uint32;
  if x32 + y32 == z32
     && y32 - x32 == z32
     && x32 as bv32 & y32 as bv32 == x32 as bv32
     && x32 as bv32 | y32 as bv32 == y32 as bv32
     && x32 as bv32 ^ y32 as bv32 == w32 as bv32
     && x32 * 3 == m32
     && x32 as bv32 >> s32 as bv32 == s32 as bv32
     && x32 as bv32 << o32 as bv32 == t32 as bv32 {
    print "operators(u32) ";
  }


  var o64: uint64 := 1 as uint64;
  var s64: uint64 := 2 as uint64;
  var w64: uint64 := 5 as uint64;
  var x64: uint64 := 8 as uint64;
  var y64: uint64 := 13 as uint64;
  var z64: uint64 := 21 as uint64;
  var m64: uint64 := 24 as uint64;
  var t64: uint64 := 16 as uint64;
  if x64 + y64 == z64
     && y64 - x64 == z64
     && x64 as bv64 & y64 as bv64 == x64 as bv64
     && x64 as bv64 | y64 as bv64 == y64 as bv64
     && x64 as bv64 ^ y64 as bv64 == w64 as bv64
     && x64 * 3 == m64
     && x64 as bv64 >> s64 as bv64 == s64 as bv64
     && x64 as bv64 << o64 as bv64 == t64 as bv64 {
    print "operators(u64)\n";
  }
  assert {:split_here} true;
  var a := 'a';
  var z := 'z';
  if a < z && z > a {
    print "char comparison\n";
  }
  
  var m := map[1 := 2];
  if 1 in m && 2 !in m && m[1] == 2{
    print "map contains acccess ";
  }
  var m2 := m + map[2 := 4] - {1};
  if 1 !in m2 && 2 in m2 {
    print "update union diff ";
  }
  var m3 := map k | 2 <= k < 4 :: k := 2*k;
  if m3 == map[3 := 6, 2 := 4] && |m3| == 2 {
    print "comprehension equality cardinality\n";
  }

  var st := {1};
  if 1 in st && 2 !in st {
    print "set contains ";
  }
  var t2 := st + {2} - {1};
  if 1 !in t2 && 2 in t2 {
    print "union diff ";
  }
  var t3 := set k | 2 <= k < 4 :: 2*k;
  if t3 == {6, 4} && |t3| == 2 {
    print "comprehension equality cardinality\n";
  }

  var s1 := [1, 2];
  var s2 := s1 + [3];
  if s1 <= s2 && s1 < s2 && s1 != s2 && !(s2 <= s1)
  && !(s2 < s1) && s2 != s1 && !(s1 == s2) {
    print "sequence prefix ";
  }
  var s3 := if |s2| == 3 then s2[2 := 4] else s2;
  if s3 == [1, 2, 4] && |s3| == 3 {
    print "sequence update cardinality ";
  }

  var s4 := if |s3| >= 3 then s3[1..3] else s3;
  if s4 == [2, 4] {
    print "sequence slice\n";
  }

  var h := multiset{1, 1, 2};
  var k := multiset{1, 2};
  if k < h && k <= h && h > k && h >= k {
    print "multiset comparison ";
  }
  if k + h == multiset{1, 1, 1, 2, 2} {
    print "union equality ";
  }
  if 1 in h && h[1] == 3 && |h| == 3 {
    print "access and cardinality";
  }
}