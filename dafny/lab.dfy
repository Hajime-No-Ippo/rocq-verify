method Abs(x: int) returns (result: int)
    requires -10 < x < 10 // contract
    ensures result >= 0
{
    if x < 0 {
        result := -x;
    } else {
        result := x;
    }
}

method {:main} TestAbs () 
{
    var x := Abs(-3);
    assert x > 0;
}