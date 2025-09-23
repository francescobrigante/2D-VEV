/*
 * Digital Environment Verification Template
 * This template is used to verify maze environments using SPIN model checker
 * 
 * The maze data will be injected by the Python verification system
 * Size: 7x7 (fixed for compatibility with existing verification setup)
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

/* Robot process */
proctype Robot() {
    int steps = 0;
    short visited[N_CELLS];
    byte r, c;

    // Initialize visited to 0
    r = 0;
    do
    :: r < H ->
        c = 0;
        do
        :: c < W -> visited[IDX(r,c)] = 0; c++
        :: else -> break
        od;
        r++
    :: else -> break
    od;

    // wait until start position is set
    (row != 0 || col != 0 || CELL(row,col) == 'S');

    assert(!AT_WALL);

    do
    :: (steps >= 10000) ->
        break

    :: AT_GOAL ->
        goal_reached = 1;
        break

    :: else ->
        visited[IDX(row,col)] = visited[IDX(row,col)] + 1;

        byte min_visit = 255;
        byte move_choice = 0;

        // North
        if
        :: (row>0 && PASSABLE(row-1,col)) ->
            if
            :: visited[IDX(row-1,col)] < min_visit -> min_visit = visited[IDX(row-1,col)]; move_choice = 1
            :: else -> skip
            fi
        :: else -> skip
        fi;

        // South
        if
        :: (row<H-1 && PASSABLE(row+1,col)) ->
            if
            :: visited[IDX(row+1,col)] < min_visit -> min_visit = visited[IDX(row+1,col)]; move_choice = 2
            :: else -> skip
            fi
        :: else -> skip
        fi;

        // East
        if
        :: (col<W-1 && PASSABLE(row,col+1)) ->
            if
            :: visited[IDX(row,col+1)] < min_visit -> min_visit = visited[IDX(row,col+1)]; move_choice = 3
            :: else -> skip
            fi
        :: else -> skip
        fi;

        // West
        if
        :: (col>0 && PASSABLE(row,col-1)) ->
            if
            :: visited[IDX(row,col-1)] < min_visit -> min_visit = visited[IDX(row,col-1)]; move_choice = 4
            :: else -> skip
            fi
        :: else -> skip
        fi;

        // Execute move
        if
        :: move_choice==1 -> row = row-1;
        :: move_choice==2 -> row = row+1;
        :: move_choice==3 -> col = col+1;
        :: move_choice==4 -> col = col-1;
        :: else -> break
        fi;

        if :: (CELL(row,col)=='a') -> has_a=1 :: else -> skip fi;
        if :: (CELL(row,col)=='b') -> has_b=1 :: else -> skip fi;
        if :: (CELL(row,col)=='c') -> has_c=1 :: else -> skip fi;

        steps++
    od;
}

init {
  atomic {
    // place to set maze data
    /* MAZE_DATA_PLACEHOLDER - This will be replaced by Python script */
    
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

/* LTL Properties */
ltl reach_goal { <> goal_reached }