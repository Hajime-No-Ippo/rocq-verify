Here's what I'd expect:
1. Preconditions (requires) — What must be true before a method executes.
2. Postconditions (ensures) — What must be true after it finishes.
3. Loop invariants (invariant) — Properties that remain true throughout a loop.
4. Assertions (assert) — Statements Dafny must mathematically prove.
5. Verification failures — Understanding why Dafny cannot prove your code correct.

{P} C {Q} Hoare Logic

method Derive(a: int, b: int) returns (result: int) 
    requires b != 0
    ensures result * b <= a
{
    result := a / b;
}


Example (1) -- Simple Return Value:


static int abs(int x) {
    if (x < 0) {
        return -x;
    }
    return x;
}


dafny
method Abs(x: int) returns (y: int) 
    ensures y >= 0
    ensures y == x || y == -x
{
    if x < 0 {
        y := -x;
    } else {
        y := x;
    }
}


Example (2) -- Preconditions:


static int divide(int a, int b) {
    if (b == 0) {
        throw new ArithmeticException();
    }
    return a / b;
}



method Divide(a: int, b: int)
    returns (result: int)
    requires b != 0
{
    result := a / b;
}


Example (3) -- Loops:


static int sum(int n) {
    int total = 0;

    for (int i = 0; i < n; i++) {
        total += i;
    }

    return total;
}



method Sum(n: nat) returns (total: int) 
    ensures total == n * (n - 1) / 2
{
    total := 0;
    var i := 0;

    while i < n
        invariant 0 <= i <= n
        invariant total == i * (i - 1) / 2
        decreases n - i
    {
        total := total + i;
        i := i + 1;
    }
}




  