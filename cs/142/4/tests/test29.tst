type t1 = array 10 of short;
type t2 = array 10 of t1;
type t3 = array 10 of t2;

main()
{
  var a : t3;
  const c = 11;
  a[1][1] = c;
}
