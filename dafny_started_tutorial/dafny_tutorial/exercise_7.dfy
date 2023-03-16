method m(n: nat)
{
  var i: int := 0;
  while i != n  // Change this. What happens? ans: still verified, because the loop guard i!=n leads to i == n after loop ends.
    invariant 0 <= i <= n
  {
    i := i + 1;
  }
  assert i == n;
}