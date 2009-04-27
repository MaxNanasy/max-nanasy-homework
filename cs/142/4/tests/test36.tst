type newType = short;

void sym1(newType &a) {
     a = 1;
}

main()
{
  const c = 11;
  ::sym1(c);
}
