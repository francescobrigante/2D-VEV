/*
 * BMC Template for finding minimum steps
 */

#define W 7
#define H 7
#define N_CELLS (W*H)

byte env[N_CELLS];

/* Conversion 2D -> 1D */
#define IDX(row,col) ((row)*W + (col))
#define CELL(row,col) env[IDX(row,col)]

/* Function to fill with values (c) in row R of environment E */
#define SET_ROW(E,R,c0,c1,c2,c3,c4,c5,c6) \
  E[IDX(R,0)]=c0; E[IDX(R,1)]=c1; E[IDX(R,2)]=c2; \
  E[IDX(R,3)]=c3; E[IDX(R,4)]=c4; E[IDX(R,5)]=c5; E[IDX(R,6)]=c6

/* State variables */
byte row=0;
byte col=0;
bit has_a=0, has_b=0, has_c=0;
bit goal_reached=0;
byte steps=0;

/* Atomic propositions */
#define AT_WALL   (CELL(row,col)=='#')
#define AT_GOAL   (CELL(row,col)=='G')
#define AT_KEY_A  (CELL(row,col)=='a')
#define AT_KEY_B  (CELL(row,col)=='b')
#define AT_KEY_C  (CELL(row,col)=='c')
#define AT_DOOR_A (CELL(row,col)=='A')
#define AT_DOOR_B (CELL(row,col)=='B')
#define AT_DOOR_C (CELL(row,col)=='C')

/* Check if cell is walkable */
#define PASSABLE(r,c) (CELL(r,c)!='#' && \
                      (CELL(r,c)!='A' || has_a) && \
                      (CELL(r,c)!='B' || has_b) && \
                      (CELL(r,c)!='C' || has_c))

/* Robot process with non-deterministic moves */
proctype Robot() {
    // Wait until start position is set
    (row != 0 || col != 0 || CELL(row,col) == 'S');
    
    assert(!AT_WALL);
    
    do
    :: (steps >= MAX_STEPS) -> break //declaration added by bmc_verifier.py
    
    :: AT_GOAL -> 
        goal_reached = 1;
        break
    
    :: else ->
        // Non-deterministic choice of valid moves
        if
        :: (row > 0 && PASSABLE(row-1, col)) -> 
            row = row - 1; steps++
        :: (row < H-1 && PASSABLE(row+1, col)) -> 
            row = row + 1; steps++
        :: (col > 0 && PASSABLE(row, col-1)) -> 
            col = col - 1; steps++
        :: (col < W-1 && PASSABLE(row, col+1)) -> 
            col = col + 1; steps++
        :: else -> break
        fi;
        
        // Collect keys
        if :: (CELL(row,col)=='a') -> has_a=1 :: else -> skip fi;
        if :: (CELL(row,col)=='b') -> has_b=1 :: else -> skip fi;
        if :: (CELL(row,col)=='c') -> has_c=1 :: else -> skip fi;
    od;
}

init {
  atomic {
    /* MAZE_DATA_PLACEHOLDER */
    
    /* Find start position */
    byte found=0; byte r=0; byte c=0;
    do
    :: (r<H && found==0) ->
         c=0;
         do
         :: (c<W && found==0) ->
              if
              :: (CELL(r,c)=='S') -> row=r; col=c; found=1
              :: else -> skip
              fi;
              c++
         :: else -> break
         od;
         r++
    :: else -> break
    od;

    assert(found==1);
  }

  run Robot()
}

/* LTL Properties -> negated for BMC */
ltl reach_goal { [] !goal_reached }