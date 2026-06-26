method IntroduceArrays() {
  var a := new int[100];
  assert a.Length == 100;
  a := new int[20];

  a[9] := a[9] + 5;

  a[6] := 2;
  a[7] := 3;
  assert a[6] == 2 && a[7] == 3;
}

method TestArrayElements(j: nat, k: nat)
  requires j < 10 && k < 10
{
  var a := new int[10];
  a[j] := 60;
  a[k] := 65;
  if j == k {
    assert a[j] == 65;
  } else {
    assert a[j] == 60;
  }
}

method ArraysAreReferences() {
  var a := new string[20];
  a[7] := "hello";

  var b := a;
  assert b[7] == "hello";

  b[7] := "hi";
  a[8] := "greetings";
  assert a[7] == "hi" && b[8] == "greetings";

  b := new string[8];
  b[7] := "long time, no see";
  assert a[7] == "hi";
  assert a.Length == 20 && b.Length == 8;
}

method MultiDimensionalArrays() {
  var m := new bool[3, 10];
  m[0, 9] := true;
  m[1, 8] := false;
  assert m.Length0 == 3 && m.Length1 == 10;
}

method SequenceExamples() {
  var greetings := ["hey", "hola", "tjena"];

  assert [1, 5, 12] + [22, 35] == [1, 5, 12, 22, 35];

  var p := [1, 5, 12, 22, 35];
  assert p[2..4] == [12, 22];
  assert p[..2] == [1, 5];
  assert p[2..] == [12, 22, 35];

  assert greetings[..1] == ["hey"];
  assert greetings[1..2] == ["hola"];
}

method PerfectStart() {
  var a := new int[3];
  a[0], a[1], a[2] := 6, 28, 496;
  assert a[..2] == [6, 28] && a[1..] == [28, 496];
  var s := a[..];
  assert s == [6, 28, 496];
  a[0] := 8128;
  assert s[0] == 6 && a[0] == 8128;
}
