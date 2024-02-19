lemma IncreasingArray(a: array<int>, n: int)
    requires forall i :: 1 <= i < a.Length ==> a[i-1] < a[i]
    requires 0 <= n < a.Length
    ensures forall i :: n < i < a.Length ==> a[n] < a[i]
    decreases a.Length - n;
{
    if n == a.Length - 1 {}
    else {
        IncreasingArray(a, n + 1);
    }
}

method Tangent(r: array<int>, x: array<int>) returns (n: bool)
    requires r.Length > 0 && x.Length > 0
    requires forall j :: 1 <= j < x.Length ==> x[j-1] < x[j]
    requires forall i, j :: (0 <= i < r.Length && 0 <= j < x.Length) ==> (r[i] > 0 && x[j] > 0)
    ensures n <==> (exists i, j :: (0 <= i < r.Length && 0 <= j < x.Length && x[j] == r[i]))
{
    var R := 0;
    var X := 0;
    n := false;
    while ((R != r.Length) && (n != true))
        invariant 0 <= R <= r.Length
        invariant n <==> (exists i, j :: (0 <= i < R && 0 <= j < x.Length && r[i] == x[j]))
        decreases r.Length - R
    {
        X := 0;
        while ((X != x.Length) && (n != true) && (x[X] <= r[R]))
            invariant 0 <= X <= x.Length
            invariant n <==> (exists i, j :: ((0 <= i < R && 0 <= j < x.Length) || (i == R && 0 <= j < X)) && r[i] == x[j])
            decreases x.Length - X
        {
            if (r[R] == x[X]) {
                n := true;
            }
            X := X + 1;
        }
        R := R + 1;
    }
}