int pid; //My pid
int num;//My ticket
int j_min;//pid of minimum holder
int min;//Minimum ticket number
int max;//Maximum ticket number
pid = *; assume(pid > 0);
num = 0;
j_min = *; assume(j_min > 0);
min = *; assume(min > 0);
max = *; assume(max >= min);

while (true){

	num = 1 + (max++);
	while(num >= min && pid > j_min){
		if(*){
			int INCREASE = *; assume(INCREASE >= 1);
			max += INCREASE;
		}
		if(*){
			int INCREASE = *; assume(INCREASE >= num);
			assume(INCREASE <= max-min);
			assume(INCREASE <= num-min);
			min += INCREASE;
			j_min = *; \\q
		}
		else{
			skip; \\p;
			if(*){
				int INCREASE = *; assume(INCREASE >= 1);
				j_min += INCREASE;
			}
		}
	}

	//CRITICAL
}