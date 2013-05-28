int main()
{
	double __attribute__ ((warning("3, 4"))) x = 3;
	double y = 4;
	x = y;
	y = 10;
	BMC_CHECK("FORMULA");
	return 10;
}
