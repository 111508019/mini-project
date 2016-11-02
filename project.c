/*****************************************************************************
 * Copyright (C) 2016 Sneha S. Chhajed (snehachhajed30@gmail.com)
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; If not, see <http://www.gnu.org/licenses/>.
 *****************************************************************************/

#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<errno.h>
#include<time.h>
#define MAX 1000000000
#define MIN 800000000
#define SIZE 10000
#define xtime(x)   ((x<<1) ^ (((x>>7) & 1) * 0x1b))
#define Multiply(x,y) (((y & 1) * x) ^ ((y>>1 & 1) * xtime(x)) ^ ((y>>2 & 1) * xtime(xtime(x))) ^ ((y>>3 & 1) * xtime(xtime(xtime(x)))) ^ ((y>>4 & 1) * xtime(xtime(xtime(xtime(x))))))
/* The number of columns comprising a state in AES. */
#define Nb 4

/*For storing rounds in AES.*/
int Nr=0;

/*For storing number of 32 bit words in AES.*/
int Nk=0;

/* in - array that holds the plain text to be encrypted.
 * out - array that holds the key for encryption.
 * state - array that holds the intermediate results during encryption.
 */
unsigned char in[16], out[16], state[4][4];
unsigned char Rkey[240];
unsigned char Key[32];

/*For storing parameters of RSA.*/
typedef struct value {
	long long int p, q, n;
	int e;
	long long int dp, dq, qinv;
}val;
int usage(int err) {
	if(err == EINVAL)
		printf("usage: ./project -e|-d <sourcefile> <destinationfile>\n\n");
	else
		printf("Open failed\n");
	return err;
}

/*To create random numbers for RSA.*/
long long int randomnum() {
	return (MAX + random() % MIN);
}

/* This function calculates (a*b)%c taking into account that a*b might overflow */
long long mul(long long a, long long b, long long c) {
    long long x = 0, y = a % c;
    while(b > 0) {
        if(b % 2 == 1) {
            x = (x + y) % c;
        }
        y = (y * 2) % c;
        b /= 2;
    }
    return x % c;
}

/* This function calculates (ab)%c */
long long mod(long long a, long long b, long long c) {
	long long x = 1, y = a; 
	while(b > 0) {
		if(b % 2 == 1)
			x = mul(x, y, c);
		y = mul(y,y,c); 
		b /= 2;
	}
	return x%c;
}

/* Rabin-MIller's primality test
 * It uses mul and mod functions for calculations
 */
int miller(long long p, long long it) {
	if(p < 2)
        	return 0;
	if(p != 2 && p % 2 == 0)
	        return 0;
    	long long s, i, a, tt, md;
	s = p - 1;
   	while(s % 2 == 0)
       		s /= 2;
    	for(i = 0; i < it; i++) {
       		a = rand() % (p - 1) + 1;
		tt = s;
        	md = mod(a, tt, p); 
       		while(tt != p - 1 && md != 1 && md != p - 1){
           	md = mul(md, md, p);
            	tt *= 2;
        }
        if(md != p - 1 && tt % 2 == 0)
            	return 0;
    	}
    	return 1;
}

/* primality test for integers*/
int IsPrime(int p) {
	int i = 2;
	for(; i < p/2; i++) {
		if(p % i == 0)
			return 0;
	}
	return 1;
}

/* calculates encryption exponent*/	
void eval(val *v, long long int z) {
	int i;
	for(i = 2; i < z; i++){
		if(z % i == 0)
			continue;
		if(IsPrime(i) && i != v->p && i != v->q) {
			v->e = i;
			break;
		}
	}
}
int dpval(val *v) {
	int z = v->p - 1;
	int t, q, x = 0, tmp = v->e;
	v->dp = 1;
 	if (z == 1)
      		return 0;
 	while (tmp > 1) {
		q = tmp / z;
	 	t = z;
	 	z = tmp % z;
	 	tmp = t;
		t = x;
	 	x = v->dp - q * x;
		v->dp = t;
	}
	if (v->dp < 0) 
       		v->dp = v->dp + (v->p - 1);
 	return 0;
}
int dqval(val *v) {
	int z = v->q - 1;
	int z0 = z, t, q, x = 0, tmp = v->e;
	v->dq = 1;
 	if (z == 1)
      		return 0;
 	while (tmp > 1) {
		q = tmp / z;
	 	t = z;
	 	z = tmp % z;
	 	tmp = t;
		t = x;
	 	x = v->dq - q * x;
		v->dq = t;
	}
	if (v->dq < 0)
       		v->dq += z0;
 	return 0;
}
int qinv(val *v) {
	int z = v->p;
	int z0 = z, t, q, x = 0, tmp = v->q;
	v->qinv = 1;
 	if (z == 1)
      		return 0;
 	while (tmp > 1) {
		q = tmp / z;
	 	t = z;
	 	z = tmp % z;
	 	tmp = t;
		t = x;
	 	x = v->qinv - q * x;
		v->qinv = t;
	}
	if (v->qinv < 0)
       		v->qinv += z0;
 	return 0;
}

/* Reads from fname1 
 * Encrypts fname1 and stores the encrypted message in fname2
 */
int encrypt_rsa(val *v, char *fname1, char *fname2) {
	FILE *fpr, *fpw;
	int x;
	char ch;
	unsigned long long int en;
	fpr = fopen(fname1, "r");
	if(fpr == NULL)
		return usage(errno);
	fpw = fopen(fname2, "w+");
	if(fpw == NULL)
		return usage(errno);
	while(fread(&ch, sizeof(char), 1, fpr)) {
		x = ch;
		en = mod(x, v->e, v->n);
		fprintf(fpw, "%llu	", en);
	}
	fclose(fpr);
	fclose(fpw);
	return 0;
}

/* Reads from fname1
 * Decrypts fname1 and store the decrypted message in fname2
 */
int decrypt_rsa(val *v, char *fname1, char *fname2) {
	FILE *fpr, *fp;
	unsigned long long int x, en, m1, m2, h;
	char m;
	fpr = fopen(fname1, "r");
	if(fpr == NULL)
		return usage(errno);
	fp = fopen(fname2, "w+");
	if(fp == NULL)
		return usage(EINVAL);
	while(fscanf(fpr, "%llu", &en) != -1) {	
		x = en;
		m1 = mod(x, v->dp, v->p);
		m2 = mod(x, v->dq, v->q);
		if(m1 < m2)
			h = (v->qinv * (m1 - m2) + v->p) % v->p;
		else 
			h = (v->qinv * (m1 - m2)) % v->p;
		m = m2 + h * v->q;
		fprintf(fp, "%c", m);
	}
	fclose(fpr);
	fclose(fp);
	return 0;
}

int RSA(char *opt, char *filename1, char *filename2) {
	FILE *fkey;
	int c1 = 0, c2 = 0, c;
	time_t t;
	long long int z;
	val v;
	char *key, *check;
	key = (char *)malloc(20);
	check = (char *)malloc(20);
	if(strcmp(opt, "-d") == 0) {
		printf("\nEnter the file containing the private key for %s file:\n", filename1);
		scanf("%s", key);
		strcpy(check, "Prkey_");
		strcat(check, filename1);
		if(strcmp(check, key)) {
			printf("Invalid key\n");
			return 1;
		}
		fkey = fopen(key, "r");
		if(fkey == NULL)
			return usage(errno);
		fscanf(fkey, "%lld%lld%lld%lld%lld", &v.p, &v.q, &v.dp, &v.dq, &v.qinv);
		decrypt_rsa(&v, filename1, filename2);
		free(key);
		free(check);
		return 0;
	}
	v.p = 1;
	v.q = 2;
	srand(time(&t));
	while(1) {
		v.p = randomnum();
		v.q = randomnum();
		c1 = miller(v.p, 20);
		c2 = miller(v.q, 20);
		if(v.p > v.q && c1 == 1 && c2 == 1)
			break;
		else 
			c1 = c2 = 0;
	}
	v.n = v.p * v.q;
	z = (v.p - 1) * (v.q - 1);	
	eval(&v,z);
	if(strcmp(opt, "-e") == 0) {
		c = encrypt_rsa(&v, filename1, filename2);
		if(c != 0) 
			return 0;
	}
	dpval(&v);
	dqval(&v);
	qinv(&v);
	strcpy(key, "Prkey_");
	strcat(key, filename2);
	fkey = fopen(key, "w+");
	if(fkey == NULL)
		return usage(errno);
	fprintf(fkey, "%lld	%lld	%lld	%lld	%lld", v.p, v.q, v.dp, v.dq, v.qinv);
	printf("\nPrivate key for %s is stored in: %s\n\n", filename2, key);
	free(key);
	fclose(fkey);
	return 0;
}
int getSBoxval(int num) {
	int sbox[256] =   {
	0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76, 
	0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0, 
	0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15, 
	0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75, 
	0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84, 
	0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf, 
	0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8, 
	0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2, 
	0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73, 
	0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb, 
	0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79, 
	0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08, 
	0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a, 
	0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e, 
	0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf, 
	0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16 };
	return sbox[num];
}
int getSBoxInvert(int num) {
	int rsbox[256] = {
	0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
	0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
	0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
	0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
	0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
	0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
	0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
	0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
	0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,	
	0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
	0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
	0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
	0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
	0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
	0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
	0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d };

return rsbox[num];
}

/* The round constant word array, Rcon[i], contains the values given by 
 * x to th e power (i-1) being powers of x.
 */
int Rcon[255] = {
	0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 
	0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 
	0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 
	0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 
	0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 
	0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 
	0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 
	0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 
	0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 
	0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 
	0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 
	0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 0x61, 0xc2, 0x9f, 
	0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb, 0x8d, 0x01, 0x02, 0x04, 
	0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f, 0x5e, 0xbc, 0x63, 
	0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 0x72, 0xe4, 0xd3, 0xbd, 
	0x61, 0xc2, 0x9f, 0x25, 0x4a, 0x94, 0x33, 0x66, 0xcc, 0x83, 0x1d, 0x3a, 0x74, 0xe8, 0xcb  };

/* This function produces round keys. */
void KeyExpansion() {
	int i, j;
	unsigned char temp[4], k;
	for(i = 0; i < Nk; i++) {
		Rkey[i*4] = Key[i*4];
		Rkey[i*4+1] = Key[i*4+1];
		Rkey[i*4+2] = Key[i*4+2];
		Rkey[i*4+3] = Key[i*4+3];
	}
	while (i < (Nb * (Nr + 1))) {
		for(j = 0; j < 4; j++) 
			temp[j] = Rkey[(i - 1) * 4 + j];
		if (i % Nk == 0) {
			k = temp[0];
			temp[0] = temp[1];
			temp[1] = temp[2];
			temp[2] = temp[3];
			temp[3] = k;
			for(j = 0; j < 4; j++) 
				temp[j] = getSBoxval(temp[j]);
			temp[0] =  temp[0] ^ Rcon[i/Nk];
		}
		else if (Nk > 6 && i % Nk == 4) {
			for(j = 0; j < 4; j++) 
				temp[j] = getSBoxval(temp[j]);			
		}
		for(j = 0; j < 4; j++)
			Rkey[i*4 + j] = Rkey[(i - Nk) * 4 + j] ^ temp[j];
		i++;
	}
}

/* This function adds the round key to state by an XOR function. */
void AddRkey(int round) {
	int i, j;
	for(i = 0; i < 4; i++) {
		for(j = 0; j < 4; j++)
			state[j][i] ^= Rkey[round * Nb * 4 + i * Nb + j];
	}
}

/* This function substitutes the values in the state matrix with values in an S-box. */
void SubBytes() {
	int i, j;
	for(i = 0; i < 4; i++) {
		for(j = 0; j < 4; j++)
			state[i][j] = getSBoxval(state[i][j]);
	}
}

/* This function substitutes the values in the state matrix with values in an rsbox. */
void InvSubBytes() {
	int i,j;
	for(i=0;i<4;i++) {
		for(j=0;j<4;j++)
			state[i][j] = getSBoxInvert(state[i][j]);
	}
}

/* This function shifts the rows in the state to the left with different offset
 * Offset = Row number.
 */
void ShiftRows() {
	unsigned char temp;

	/* Rotate first row 1 columns to left */
	temp = state[1][0];
	state[1][0] = state[1][1];
	state[1][1] = state[1][2];
	state[1][2] = state[1][3];
	state[1][3] = temp;

	/* Rotate second row 2 columns to left */
	temp = state[2][0];
	state[2][0] = state[2][2];
	state[2][2] = temp;

	temp = state[2][1];
	state[2][1] = state[2][3];
	state[2][3] = temp;

	/* Rotate third row 3 columns to left */
	temp = state[3][0];
	state[3][0] = state[3][3];
	state[3][3] = state[3][2];
	state[3][2] = state[3][1];
	state[3][1] = temp;
}

/* This function shifts the rows in the state to the right with different offset
 * Offset = Row number.
 */
void InvShiftRows() {
	unsigned char temp;

	/* Rotate first row 1 columns to right */
	temp=state[1][3];
	state[1][3]=state[1][2];
	state[1][2]=state[1][1];
	state[1][1]=state[1][0];
	state[1][0]=temp;

	/* Rotate second row 2 columns to right */	
	temp=state[2][0];
	state[2][0]=state[2][2];
	state[2][2]=temp;

	temp=state[2][1];
	state[2][1]=state[2][3];
	state[2][3]=temp;

	/* Rotate third row 3 columns to right */
	temp=state[3][0];
	state[3][0]=state[3][1];
	state[3][1]=state[3][2];
	state[3][2]=state[3][3];
	state[3][3]=temp;
}
void MixColumns()
{
	int i;
	unsigned char Tmp,Tm,t;
	for(i=0;i<4;i++)
	{	
		t=state[0][i];
		Tmp = state[0][i] ^ state[1][i] ^ state[2][i] ^ state[3][i] ;
		Tm = state[0][i] ^ state[1][i] ; 
		Tm = xtime(Tm); 
		state[0][i] ^= Tm ^ Tmp ;
		Tm = state[1][i] ^ state[2][i] ; 
		Tm = xtime(Tm); 
		state[1][i] ^= Tm ^ Tmp ;
		Tm = state[2][i] ^ state[3][i] ; 
		Tm = xtime(Tm); 
		state[2][i] ^= Tm ^ Tmp ;
		Tm = state[3][i] ^ t ;
		Tm = xtime(Tm); 
		state[3][i] ^= Tm ^ Tmp ;
	}
}
void InvMixColumns() {
	int i;
	unsigned char a,b,c,d;
	for(i=0;i<4;i++) {	
		a = state[0][i];
		b = state[1][i];
		c = state[2][i];
		d = state[3][i];state[0][i] = Multiply(a, 0x0e) ^ Multiply(b, 0x0b) ^ Multiply(c, 0x0d) ^ Multiply(d, 0x09);
		state[1][i] = Multiply(a, 0x09) ^ Multiply(b, 0x0e) ^ Multiply(c, 0x0b) ^ Multiply(d, 0x0d);
		state[2][i] = Multiply(a, 0x0d) ^ Multiply(b, 0x09) ^ Multiply(c, 0x0e) ^ Multiply(d, 0x0b);
		state[3][i] = Multiply(a, 0x0b) ^ Multiply(b, 0x0d) ^ Multiply(c, 0x09) ^ Multiply(d, 0x0e);
	}
}
void encrypt_aes() {
	int i, j, round = 0;
	for(i = 0; i < 4; i++) {
		for(j = 0; j < 4; j++)
			state[j][i] = in[i*4 + j];
	}
	AddRkey(0); 
	for(round = 1; round < Nr; round++)
	{
		SubBytes();
		ShiftRows();
		MixColumns();
		AddRkey(round);
	}
	
	/* The MixColumns function is not here in the last round. */
	SubBytes();
	ShiftRows();
	AddRkey(Nr);
	for(i = 0; i < 4; i++) {
		for(j = 0; j < 4; j++)
			out[i * 4 + j] = state[j][i];
	}
}
void decrypt_aes() {
	int i,j,round=0;
	for(i=0;i<4;i++) {
		for(j=0;j<4;j++)
			state[j][i] = in[i*4 + j];
	}
	AddRkey(Nr); 
	for(round=Nr-1;round>0;round--)
	{
		InvShiftRows();
		InvSubBytes();
		AddRkey(round);
		InvMixColumns();
	}
	InvShiftRows();
	InvSubBytes();
	AddRkey(0);
	for(i=0;i<4;i++) {
		for(j=0;j<4;j++)
			out[i*4+j]=state[j][i];
	}
}

int AES(char *opt, char *filename1, char *filename2) {
	FILE *fp, *fpw, *fkey;
	int i, j, k;
	int tmp[16];
	char *temp;
	char *skey, *check;
	skey = (char *)malloc(20);
	check = (char *)malloc(20);
	temp = (char *)malloc(100);
	fp = fopen(filename1, "r");
	if(fp == NULL)
		return usage(errno);
	Nr = 128;
	Nk = Nr / 32;
	Nr = Nk + 6;
	if(strcmp(opt, "-e") == 0) {
		strcpy(skey, "Sykey_");
		strcat(skey, filename2);
		fkey = fopen(skey, "w+");
		if(fkey == NULL) 
			return usage(errno);
		printf("Enter the key(16 bytes):\n");
		for(i = 0; i < Nk * 4; i++) {
			scanf("%c",&temp[i]);
			fprintf(fkey, "%c", temp[i]);
			Key[i] = temp[i];
		}
		printf("\nKey is stored in %s file\n\n", skey);
		free(temp);
		fpw = fopen(filename2, "w+");
		if(fpw == NULL)
			return usage(errno);
		while((j = fread(in, sizeof(char), 16, fp))) {
			if(in[0] == 10 && in[1] == 0)
				break;
			if(j < 16) 
				for(; j < 16; j++)
					in[j] = 32;
			KeyExpansion();
			encrypt_aes();
			for(i = 0; i < 16; i++)
				fprintf(fpw, "%d ", out[i]);
		}
	}
	else if(strcmp(opt, "-d") == 0) {
		printf("\nEnter the file containing the symmetric key for %s file:\n", filename1);
		scanf("%s", skey);
		strcpy(check, "Sykey_");
		strcat(check, filename1);
		if(strcmp(check, skey)) {
			printf("Invalid key\n");
			return 1;
		}
		fkey = fopen(skey, "r");
		if(fkey == NULL) 
			return usage(errno);
		for(k = 0; k < Nk * 4; k++) {
			fread(&temp[k], sizeof(char), 1, fkey);
			Key[k] = temp[k];
		}
		fpw = fopen(filename2, "w+");
		if(fpw == NULL)
			return usage(errno);
		i = 0;
		while(1) {
			while(i < 16) {
				j = fscanf(fp, "%d", &tmp[i]);
				if(j == -1) 
					break;
				else
					i++;
			}
			if(j == -1)
				break;
			for(j = 0; j < 16; j++) 
				in[j] = tmp[j];
			KeyExpansion();
			decrypt_aes();
			for(i = 0; i < 16; i++)
				fprintf(fpw, "%c", out[i]);
			i = 0;
		}
	}
	free(skey);
	free(check);
	fclose(fkey);
	fclose(fpw);
	fclose(fp);
	return 0;

}
int main(int argc, char *argv[]) {
	if(strcmp(argv[1], "-h") == 0) 
		return usage(EINVAL);
	if(argc != 4)
		return usage(EINVAL);
	int choice;
	if(strcmp(argv[1], "-e") == 0) {
		printf("\nChoose the algorithm for encryption:\n1.RSA(Asymmetric key)\n2.AES(Symmetric key)\n");
		scanf("%d", &choice);
		switch(choice) {
			case 1:
				RSA(argv[1], argv[2], argv[3]);
				break;
			case 2:
				AES(argv[1], argv[2], argv[3]);
				break;
			default:
				printf("Incorrect choice");
				break;
		}
	}
	else if(strcmp(argv[1], "-d") == 0) {
		printf("\nChoose the algorithm using which encrypted file %s was created:\n1.RSA(Asymmetric key)\n2.AES(Symmetric key)\n", argv[2]);
		scanf("%d", &choice);
		switch(choice) {
			case 1:
				RSA(argv[1], argv[2], argv[3]);
				break;
			case 2:
				AES(argv[1], argv[2], argv[3]);
				break;
			default:
				printf("Incorrect choice");
				break;
		}
	}
	else
		return usage(EINVAL);
}
