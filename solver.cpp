/*
Solver -- automatic solver for Ten Drops

Author: fwjmath (fwjmath@gmail.com)

Last update: 2010/07/28 0:01 UTC+2

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
*/

#include <stdio.h>
#include <stdlib.h>

#define HEAPSIZE 600000  // Size of board storing heap, can be changed to for memory usage

struct dropstate{
	int dest; // Destination of this flying drop
	int dir; // Flying direction. 0 right; 1 down; 2 left; 3 up;
};

// A stack to store flying drops.
struct stack{
	int cnt;
	struct dropstate drops[36];
};

struct dropboard{
	int board[36]; // Board status. board[(i-1)*6+j-1] means the value at i-th line j-th column.
	int move[30]; // Move path from initial board to this board
	int d, dc, mvc, lastinc; // Drops in hand, drops on board, number of moves, last incremental move
};

// Node in heap, used as priority queue
struct node{
	int eval;
	struct dropboard mydb;
};

FILE* frecord;
struct stack* moving[12]; // Flying drops, arranged by time
struct stack* totreat; 
struct stack* tmpstack[12];
struct dropboard myboard, bestsol;
struct node heap[HEAPSIZE+1]; // Heap for best-first search
int dfstopdrop=0, dfscutoff, minmove=360; // Drops in hand for best solution, search depth cutoff for depth-first search, minimum move count of known solutions
int dfscount=0, bfscount=0; // Number of expansions in depth-first search and in best-first search

// Convert from (i,j) to board index
__inline int cvt(int a, int b){ return a*6+b; }

// Evaluation function of board
__inline int evaluation(struct dropboard* db){
	int e=0;
	int* arr=db->board;
	for(int i=0;i<36;i++){
		switch(arr[i]){
		case 0:
			e+=10; break;
		case 4:
			e+=9; break;
		case 2:
			e+=2; break;
		case 3:
			e+=5; break;
		default:;
		}
	}
	e+=db->d*25;
	e-=db->mvc*30;
	return e;
}

// Initialization, reading initial board
void init(){
	char c;
	scanf("%d",&myboard.d);
	scanf("%c",&c);
	for(int i=0;i<6;i++){
		for(int j=0;j<6;j++){
			scanf("%c",&c);
			if(c!='0') myboard.dc++;
			myboard.board[cvt(i,j)]=c-'0';
		}
		scanf("%c",&c);
	}
	myboard.mvc=0;
	myboard.lastinc=0;
	bestsol=myboard;
	for(int i=0;i<12;i++) moving[i]=(struct stack*)malloc(sizeof(struct stack));
	return;
}

// Utility to print board status in file
void printboard(struct dropboard* db){
	int* board=db->board;
	fprintf(frecord, "%d\n", db->d);
	for(int i=0;i<6;i++){
		int tmp=6*i;
		fprintf(frecord, "%d%d%d%d%d%d\n", board[tmp],board[tmp+1],board[tmp+2],board[tmp+3],board[tmp+4],board[tmp+5]);
	}
	return;
}

// Utility to print solution containing in a board
void printsol(struct dropboard* db){
	int* sol=db->move;
	int mv=db->mvc;
	if(db->dc!=0){
		printf("No solution or error.\n");
		return;
	}
	printf("Here is a solution with %d drops after %d dfs and %d bfs: \n", db->d, dfscount, bfscount);
	for(int i=0;i<mv;i++) printf("%d ",(sol[i]/6+1)*10+1+(sol[i]%6));
	printf("\n");
	bestsol=*db;
	return;
}

// Utility to print solution containing in a board
void printsol_f(struct dropboard* db){
	int* sol=db->move;
	int mv=db->mvc;
	if(db->dc!=0){
		fprintf(frecord, "No solution or error.\n");
		return;
	}
	fprintf(frecord, "Solution with %d drops after %d dfs and %d bfs: \n", db->d, dfscount, bfscount);
	for(int i=0;i<mv;i++) fprintf(frecord, "%d ",(sol[i]/6+1)*10+1+(sol[i]%6));
	fprintf(frecord, "\n");
	return;
}

// Simulate a move in a board, pos is the position of move in board index.
// Drops fly across a square in 2 unities of time, but arrive at the next drop in 1 unity of time
__inline void dropin(int pos, struct dropboard* db){
	int* board=db->board;
	if(board[pos]!=4){
		board[pos]++;
		db->d--;
		return;
	}else if(board[pos]==0){
		printf("Error occured in dropin.\n");
		return;
	}
	int flycount=1, burstcount=0;
	db->d--;
	for(int i=0;i<12;i++) moving[i]->cnt=0;
	moving[0]->cnt=1;
	moving[0]->drops[0].dest=pos;
	moving[0]->drops[0].dir=0;
	while(true){
		// Update arriving drops
		totreat=moving[0];
		for(int i=0;i<totreat->cnt;i++){
			int mypos = totreat->drops[i].dest;
			if(board[mypos]!=0){
				board[mypos]++;
			}else{
				int lookpos, limitpos;
				switch(totreat->drops[i].dir){
				case 0:
					lookpos=mypos+1;
					limitpos=(mypos/6+1)*6;
					while((lookpos<limitpos)&&(board[lookpos]==0)) lookpos++;
					if(lookpos!=limitpos){
						limitpos=(lookpos-mypos)<<1;
						moving[limitpos]->drops[moving[limitpos]->cnt].dir=totreat->drops[i].dir;
						moving[limitpos]->drops[moving[limitpos]->cnt].dest=lookpos;
						moving[limitpos]->cnt++;
						flycount++;
					}
					break;
				case 1:
					lookpos=mypos+6;
					while((lookpos<36)&&(board[lookpos]==0)) lookpos+=6;
					if(lookpos<36){
						limitpos=(lookpos-mypos)/3;
						moving[limitpos]->drops[moving[limitpos]->cnt].dir=totreat->drops[i].dir;
						moving[limitpos]->drops[moving[limitpos]->cnt].dest=lookpos;
						moving[limitpos]->cnt++;
						flycount++;
					}
					break;
				case 2:
					lookpos=mypos-1;
					limitpos=(mypos/6)*6;
					while((lookpos>=limitpos)&&(board[lookpos]==0)) lookpos--;
					if(lookpos>=limitpos){
						limitpos=(mypos-lookpos)<<1;
						moving[limitpos]->drops[moving[limitpos]->cnt].dir=totreat->drops[i].dir;
						moving[limitpos]->drops[moving[limitpos]->cnt].dest=lookpos;
						moving[limitpos]->cnt++;
						flycount++;
					}
					break;
				default:
					lookpos=mypos-6;
					while((lookpos>=0)&&(board[lookpos]==0)) lookpos-=6;
					if(lookpos>=0){
						limitpos=(mypos-lookpos)/3;
						moving[limitpos]->drops[moving[limitpos]->cnt].dir=totreat->drops[i].dir;
						moving[limitpos]->drops[moving[limitpos]->cnt].dest=lookpos;
						moving[limitpos]->cnt++;
						flycount++;
					}
				}
			}
		}
		flycount-=totreat->cnt;
		totreat->cnt=0;
		// Treat bursting drops
		for(int i=0;i<36;i++){
			if(board[i]>4){
				burstcount++;
				board[i]=0;
				int lookpos=i+1;
				int limitpos=(i/6+1)*6;
				while((lookpos<limitpos)&&(board[lookpos]==0)) lookpos++;
				if(lookpos<limitpos){
					limitpos=((lookpos-i)<<1)-1;
					moving[limitpos]->drops[moving[limitpos]->cnt].dir=0;
					moving[limitpos]->drops[moving[limitpos]->cnt].dest=lookpos;
					moving[limitpos]->cnt++;
					flycount++;
				}
				lookpos=i-1;
				limitpos=(i/6)*6;
				while((lookpos>=limitpos)&&(board[lookpos]==0)) lookpos--;
				if(lookpos>=limitpos){
					limitpos=((i-lookpos)<<1)-1;
					moving[limitpos]->drops[moving[limitpos]->cnt].dir=2;
					moving[limitpos]->drops[moving[limitpos]->cnt].dest=lookpos;
					moving[limitpos]->cnt++;
					flycount++;
				}
				lookpos=i+6;
				while((lookpos<36)&&(board[lookpos]==0)) lookpos+=6;
				if(lookpos<36){
					limitpos=(lookpos-i)/3-1;
					moving[limitpos]->drops[moving[limitpos]->cnt].dir=1;
					moving[limitpos]->drops[moving[limitpos]->cnt].dest=lookpos;
					moving[limitpos]->cnt++;
					flycount++;
				}
				lookpos=i-6;
				while((lookpos>=0)&&(board[lookpos]==0)) lookpos-=6;
				if(lookpos>=0){
					limitpos=(i-lookpos)/3-1;
					moving[limitpos]->drops[moving[limitpos]->cnt].dir=3;
					moving[limitpos]->drops[moving[limitpos]->cnt].dest=lookpos;
					moving[limitpos]->cnt++;
					flycount++;
				}
			}
		}
		// Go ahead in time by rotating pointers in "moving"
		if(flycount==0) break;
		int ptr=1;
		while((ptr<12)&&(moving[ptr]->cnt==0)) ptr++;
		for(int i=0;i<ptr;i++) tmpstack[i]=moving[i];
		for(int i=ptr;i<12;i++) moving[i-ptr]=moving[i];
		for(int i=0;i<ptr;i++) moving[11-i]=tmpstack[ptr-i-1];
	}
	db->d+=burstcount/3;
	db->dc-=burstcount;
	return;
}

// A depth-first search to solve a board (usually with few drops, but is general for all possible board).
void dfsboard(struct dropboard db, int startpos){
	if((db.dc==0)&&(db.d>dfstopdrop)){
		dfstopdrop=db.d;
		printsol(&db);
		if(db.mvc<dfscutoff) dfscutoff=db.mvc;
		if(db.mvc<minmove) minmove=db.mvc;
		return;
	}
	if((db.d==0)||(db.mvc>=minmove)||(db.d+db.dc/3<=dfstopdrop)||(db.mvc==24)) return;
	dfscount++;
	struct dropboard mydb=db;
	for(int i=startpos;i<36;i++){
		if(mydb.board[i]==4){
			dropin(i,&mydb);
			mydb.move[mydb.mvc]=i;
			mydb.mvc++;
			dfsboard(mydb,0);
			mydb=db;
		}
	}
	for(int i=startpos;i<36;i++){
		if(mydb.board[i]==3){
			mydb.board[i]++;
			mydb.d--;
			mydb.move[mydb.mvc]=i;
			mydb.mvc++;
			dfsboard(mydb,i);
			mydb=db;
		}
	}
	for(int i=startpos;i<36;i++){
		if(mydb.board[i]==2){
			mydb.board[i]++;
			mydb.d--;
			mydb.move[mydb.mvc]=i;
			mydb.mvc++;
			dfsboard(mydb,i);
			mydb=db;
		}
	}
	for(int i=startpos;i<36;i++){
		if(mydb.board[i]==1){
			mydb.board[i]++;
			mydb.d--;
			mydb.move[mydb.mvc]=i;
			mydb.mvc++;
			dfsboard(mydb,i);
			mydb=db;
		}
	}
	return;
}

// A best-first search using a heap as priority queue.
void bfsheap(struct dropboard db){
	int heapcount;
	struct dropboard localdb, tmpdb;
	for(int i=0;i<=HEAPSIZE;i++) heap[i].eval=-1;
	heap[1].eval=evaluation(&db);
	heap[1].mydb=db;
	heapcount=1;
	while(heapcount>0){
		// Extract board with maximal evaluation
		localdb=heap[1].mydb;
		heap[1]=heap[heapcount];
		heap[heapcount].eval=-1;
		heapcount--;
		int pos=1, bigger;
		while((pos<<1)<=heapcount){
			bigger=pos;
			if(((pos<<1)<=heapcount)&&(heap[pos<<1].eval>heap[pos].eval)) bigger=pos<<1;
			if((((pos<<1)+1)<=heapcount)&&(heap[(pos<<1)+1].eval>heap[bigger].eval)) bigger=(pos<<1)+1;
			if(bigger!=pos){
				struct node tmpnode;
				tmpnode=heap[pos];
				heap[pos]=heap[bigger];
				heap[bigger]=tmpnode;
				pos=bigger;
			}else{
				break;
			}
		}
		// Brave pruning here! When the heap is nearly full, drop half of the boards in the heap.
		if(heapcount>HEAPSIZE-40){
			for(int i=heapcount-(HEAPSIZE>>1)+1;i<=heapcount;i++) heap[i].eval=-1;
			heapcount-=(HEAPSIZE>>1);
			// printf("Pruned some of the nodes.\nBest board: eval %d, move %d\n", evaluation(&localdb), localdb.mvc);
		}
		// When current board is small, do a depth-first search, else expand it in best-first manner.
		if(localdb.dc<=11){
			dfscutoff=360;
			dfsboard(localdb,localdb.lastinc);
		}else{
			// Still pruning! Prune if current board has too much move or can not possibly achieve better drop count in hand at last
			if((localdb.mvc<minmove)&&(localdb.dc/3+localdb.d>dfstopdrop)){
				for(int i=localdb.lastinc;i<36;i++){
					if(localdb.board[i]>=1){
						tmpdb=localdb;
						dropin(i,&tmpdb);
						// More pruning! Same reason as above. If the board runs out of drops in hand, prune it.
						if(tmpdb.dc/3+tmpdb.d<=dfstopdrop) continue;
						if(tmpdb.d<=0) continue;
						tmpdb.move[tmpdb.mvc]=i;
						tmpdb.mvc++;
						if(tmpdb.dc==0) dfsboard(tmpdb,0);
						if(localdb.board[i]==4) tmpdb.lastinc=0; else tmpdb.lastinc=i;
						// Insert new board in heap
						heapcount++;
						bfscount++;
						heap[heapcount].mydb=tmpdb;
						heap[heapcount].eval=evaluation(&tmpdb);
						int tpos=heapcount;
						while((tpos<1)&&(heap[tpos].eval>heap[tpos>>1].eval)){
							struct node tmpnode;
							tmpnode=heap[tpos];
							heap[tpos]=heap[tpos>>1];
							heap[tpos>>1]=tmpnode;
							tpos>>=1;
						}
					}
				}
			}
		}
	}
	return;
}

int main(){
	char c;
	init();
	frecord=fopen("record.txt","a");
	printboard(&myboard);
	bfsheap(myboard);
	printf("End of computation.\n");
	//printsol(&bestsol);
	printsol_f(&bestsol);
	fclose(frecord);
	scanf("%c",&c);
	return 0;
}

/*
test case:

9 drops -> 11 drops

9
103233
202140
301440
121040
333321
022432

22
130422
200021
011203
400110
220232
322332

*/