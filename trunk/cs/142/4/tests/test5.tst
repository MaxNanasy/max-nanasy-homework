type t1 = array 10 of int;
type t2 = t1;
type t3 = t2;
type t4 = t3;

main()
{
  var a : t4;

  a = 1;

}