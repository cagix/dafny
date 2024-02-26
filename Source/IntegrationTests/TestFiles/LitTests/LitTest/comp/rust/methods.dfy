// NONUNIFORM: Temporary development of the Rust compiler
// RUN: %baredafny run --target=rs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Never assigning means j does not need tracker.
method TakeOne(x: int, y: int) returns (j: int)
{
  if x + y > 0 {
    return 3;
  }
  return 1;
}

// Needs assignment trackers for out variables
method ReturnDifference(x: int, y: int) returns (lessThan: bool, diff: nat)
  ensures x + (if lessThan then diff else 0-diff) == y
{
  if x < y {
    lessThan := true;
    diff := y - x;
    return;
  }
  lessThan := false;
  diff := x - y;
}


// Needs assignment trackers for out variables
method ReturnDifferenceTuple(x: int, y: int) returns (output: (bool, nat))
  ensures x + (if output.0 then output.1 else 0-output.1) == y
{
  var lessThan, diff;
  if x < y {
    lessThan := true;
    diff := y - x;
    return (lessThan, diff);
  }
  lessThan := false;
  diff := x - y;
  return (lessThan, diff);
}


method Main() {
  var j := TakeOne(3, -2);
  expect j == 3;
  var lt := ReturnDifferenceTuple(2, 5);
  var l, t := lt.0, lt.1;
  expect l;
  expect t == 3;
  l, t := ReturnDifference(6, 2);
  expect !l;
  expect t == 4;
}