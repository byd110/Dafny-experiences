method m()
{
  var i, n := 0, 20;
  while i != n
    decreases n - i //the error is: decreases expression must be bounded below by 0 at end of loop iteration. this means we need to add a lower boundary for decreasing var. one solution invariant is written below.
    // invariant n - i >= 0
  {
    i := i + 1;
  }
}