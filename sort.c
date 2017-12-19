
#include <stdio.h>

/*@ predicate Swap{L1,L2}(int *a, integer l, integer i, integer j) =
     \at(a[i],L1) == \at(a[j],L2) &&
     \at(a[j],L1) == \at(a[i],L2) &&
     \forall integer k; k != i && k != j
         ==> \at(a[k],L1) == \at(a[k],L2);
  */

/*@ predicate Sorted(int *a, integer l, integer h) =
     \forall integer i, j; l <= i <= j <= h ==> a[i] <= a[j];
  */



/*@ requires \valid(t+i) && \valid(t+j);
requires l>0;
requires 0 <= i < l;
requires 0 <= j < l;
   assigns t[i],t[j];
   ensures Swap{Old,Here}(t,l,i,j);
  */


void swap(int *t, int l, int i,int j){
  int tmp;
  tmp = t[i];
  t[i] = t[j];
  t[j] = tmp;
  return;
}


/*@ requires l >0;
requires \valid(t + (0..l-1));
assigns t[0..l-1];

ensures (\forall integer a; 0<=a <l
 ==> (\exists integer b; 0<= b < l
 ==> \at(t[b],Old)== \at(t[a],Here) ));

ensures Sorted(t, 0, l-1);
*/
void sort(int *t, int l) { 
  int i;
  int j;
  i=j=0;
  /*@ loop assigns i,j,t[0..l-1];
  loop invariant l;
  loop invariant 0 <= i <= l;
  
  loop invariant 0 < i <= l ==> \forall int a,b; 0 <= b <= l-i <= a <=l-1  ==> t[a]>=t[b];  
  */
  for (i=0;i<l;i++) {

  	/*@ loop assigns j,t[0..l-1];
    loop invariant l;
  	loop invariant 0<= j <= l-1; 
  	loop invariant 0 < j <l-1 ==>\forall int a; 0<= a <= j ==> t[a]<=t[j]; 
    loop variant l-j;
    
  	*/
    for (j=0;j<l-1;j++) {
      if (t[j] > t[j+1]){ 	
      	swap(t,l ,j, j+1);
    }
  }
}
}



/*@ requires \true;
  @ ensures \result == 0;
  @*/
int main() {
  int t[10] = {4,3,8,8,1,0,7,2,9,1};
  affiche(t,10);
  sort(t,10);
  affiche(t,10);
  return 0;
}