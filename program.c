#include<stdio.h>
#include<stdlib.h>
#include<math.h>
#include<string.h>
#include<errno.h>
#define MAX 10000000
#define MIN 8000000
#define SIZE 500
typedef struct value{
	long long int p,q;
	int e[10];
	int d[10];
	long long int n;
}val;
char en[SIZE], emsg[SIZE];
long long int *tmp;
int usage(int err){
	if(err == EINVAL)
		perror("usage: ./program <filename1> <filename2> \n");
	else
		perror("Open failed\n");
	return err;
}
	
long long int randomnum(){
	return (MAX + random() % MIN);
}
long long mul(long long a,long long b,long long c){
    long long x = 0,y=a%c;
    while(b > 0){
        if(b%2 == 1){
            x = (x+y)%c;
        }
        y = (y*2)%c;
        b /= 2;
    }
    return x%c;
}
long long mod(long long a,long long b,long long c){
	long long x=1,y=a; 
	while(b > 0){
		if(b%2 == 1)
			x=mul(x,y,c);
		y = mul(y,y,c); 
		b /= 2;
	}
	return x%c;
}
 
int miller(long long p,long long it){
	if(p<2)
        	return 0;
	if(p!=2 && p%2==0)
	        return 0;
    	long long s=p-1;
   	while(s%2==0)
       		s/=2;
	long long i;
    	for(i=0;i<it;i++){
       		long long a=rand()%(p-1)+1,tt=s;
        	long long md=mod(a,tt,p);
       		while(tt!=p-1 && md!=1 && md!=p-1){
           	md=mul(md,md,p);
            	tt *= 2;
        }
        if(md!=p-1 && tt%2==0)
            	return 0;
    	}
    	return 1;
}
int isprime(int p){
	int i=2;
	for(;i<p/2;i++){
		if(p%i == 0)
			return 0;
	}
	return 1;
}	
void eval(val *v, long long int z){
	int k=0, i=2;
	for(;i<z;i++){
		if(z%i == 0)
			continue;
		if(isprime(i) && i != v->p && i != v->q){
			v->e[k] = i;
			k++;
		}
		if(k == 10)
			break;
	}
}
void dval(val *v,long long int z, int i);
int encry(val *v,char *str, char *fname){
	FILE *fp;
	fp = fopen(fname, "w+");
	if(fp == NULL)
		return usage(errno);
	int i=0, k=1, j, x, len;
	len = strlen(str);
	tmp = (long long int *)malloc(len);
	while(i != len){
			k = 1;
			x = str[i] - 96;
		for(j=0; j < v->e[0]; j++){
			k = k * x;
			k = k % v->n;
		}
		tmp[i] = k;
		en[i] = k+96;
		if(fabs(en[i]) < 48)
			emsg[i] = 48 + (48 - fabs(en[i]));
		else if(fabs(en[i]) > 127)
			emsg[i] = 127 - (fabs(en[i]) - 127);
		else
			emsg[i] = fabs(en[i]);
		i++;
	}
	en[i] = '\0';
	emsg[i] = '\0';
	printf("\nEncrypted message-%s\n",emsg);
	fprintf(fp, "%s", emsg);
	return 0;
}
void decrypt(char *);
int main(int argc, char *argv[]){
	if(argc != 3)
		return usage(EINVAL);
	int c1 = 0,c2 = 0,i=0;
	long long int z;
	val v;
	char *str;
	while(1){
		if(c1 != 1){
			v.p = randomnum();
			c1 = miller(v.p, 20);
		}
		if(c2 != 1){
			v.q = randomnum();
			c2 = miller(v.q, 20);
		}
		if(c1 ==1 && c2 == 1)
			break;
	}
	v.n = v.p * v.q;
	z = (v.p - 1) * (v.q - 1);
	eval(&v,z);
	//for(i=0 ;i<10; i++)
	//	dval(&v, z, i);
	str = (char *)malloc(SIZE);
	printf("Enter the message:\n");
	i = 0;
	while(i<SIZE){
		scanf("%c", &str[i]);
		if(str[i] == '\n')
			break;
		i++;
	}
	return encry(&v, str, argv[1]);
}	
	

