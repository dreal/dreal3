struct account {
   int account_number;
   char *first_name;
   char *last_name;
   float balance;
};

int main()
{
	struct account s;
	s.account_number = 3;
	return 0;
}
