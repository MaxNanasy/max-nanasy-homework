type t1 = array 10 of int;
int proc(int a) { return 1; }
main()
{
  var a : t1;
  const c = 11;
  a[1] = ::proc(a[2],a[3]);
}
