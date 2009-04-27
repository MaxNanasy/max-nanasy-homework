type newType = short;
var b : int;

void sym1() {
  type newType = int;
  var a : newType;
  const c = 11;
  b = c;
  a = b + c;
}
main()
{
  var a : newType;
  const c = 11;
  b = c;
  a = b + 1;
}
