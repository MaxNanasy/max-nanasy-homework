type t1 = array 10 of int;
short proc(short a) { return a; }
main()
{
  var a : t1;
  const c = 11;
  a[1] = ::proc(c);
  if (a[1] == c)  {
     ERROR
  }
}
