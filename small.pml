/*
  *         Virtual Environment Validator
  *         Symbols:
  *           # wall, @ free, S start, G goal
  *           a,b,c keys <-> A,B,C doors
*/

#define W 7
#define H 7
#define N_CELLS (W*H)
#define SELECT_ENV 1  /* 1,2,3 */

/* 1D environments */
byte env1[N_CELLS]; /* Correct environment */
byte env2[N_CELLS]; /* Unreachable Goal because of walls */
byte env3[N_CELLS]; /* Unreachable Goal because key 'a' is unreachable */

byte env[N_CELLS];  /* active environment */

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
    short visited[N_CELLS]; // matrix to count visits -> useful to provide fairness
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
    printf("Robot starts at (%d,%d), cell='%c'\n", row, col, CELL(row,col));

    assert(!AT_WALL);

    do
    :: (steps >= 70000) ->
        printf("Max steps reached, breaking\n");
        break

    :: AT_GOAL ->
        printf("Goal reached!\n");
        goal_reached = 1;
        // break

    :: else ->
        printf("Step %d: at (%d,%d), cell='%c'\n", steps, row, col, CELL(row,col));
        visited[IDX(row,col)] = visited[IDX(row,col)] + 1;

        byte min_visit = 255;   // to find the least visited cell
        byte move_choice = 0;   // 1=N, 2=S, 3=E, 4=W

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
        :: move_choice==1 -> printf("Chose North\n"); row = row-1;
        :: move_choice==2 -> printf("Chose South\n"); row = row+1;
        :: move_choice==3 -> printf("Chose East\n"); col = col+1;
        :: move_choice==4 -> printf("Chose West\n"); col = col-1;
        :: else -> printf("No valid moves, robot stuck\n"); break
        fi;

        printf("After move: at (%d,%d), cell='%c'\n", row, col, CELL(row,col));

        if :: (CELL(row,col)=='a') -> has_a=1; printf("Collected key a\n") :: else -> skip fi;
        if :: (CELL(row,col)=='b') -> has_b=1; printf("Collected key b\n") :: else -> skip fi;
        if :: (CELL(row,col)=='c') -> has_c=1; printf("Collected key c\n") :: else -> skip fi;

        steps++
    od;
}



/* Choose between environments */
#if SELECT_ENV==1
#define SRC env1
#elif SELECT_ENV==2
#define SRC env2
#elif SELECT_ENV==3
#define SRC env3
#else
#error "SELECT_ENV must be 1..3"
#endif

/* Init process */
init {
  atomic {
    /* Env1 - Solvable */
    SET_ROW(env1,0,'#','#','#','#','#','#','#');
    SET_ROW(env1,1,'#','S','@','@','a','@','#');
    SET_ROW(env1,2,'#','@','#','#','@','@','#');
    SET_ROW(env1,3,'#','@','@','A','@','#','#');
    SET_ROW(env1,4,'#','#','@','#','@','@','#');
    SET_ROW(env1,5,'#','@','@','@','@','G','#');
    SET_ROW(env1,6,'#','#','#','#','#','#','#');

    /* Env2 - Goal unreachable by walls */
    SET_ROW(env2,0,'#','#','#','#','#','#','#');
    SET_ROW(env2,1,'#','S','@','@','a','@','#');
    SET_ROW(env2,2,'#','@','#','#','@','@','#');
    SET_ROW(env2,3,'#','@','@','A','#','#','#');
    SET_ROW(env2,4,'#','#','@','#','#','G','#');
    SET_ROW(env2,5,'#','@','@','@','@','#','#');
    SET_ROW(env2,6,'#','#','#','#','#','#','#');

    /* Env3 - Key 'a' unreachable */
    SET_ROW(env3,0,'#','#','#','#','#','#','#');
    SET_ROW(env3,1,'#','S','@','@','#','@','#');
    SET_ROW(env3,2,'#','@','#','#','#','@','#');
    SET_ROW(env3,3,'#','@','@','A','@','@','#');
    SET_ROW(env3,4,'#','#','#','#','@','G','#');
    SET_ROW(env3,5,'#','#','a','#','@','@','#');
    SET_ROW(env3,6,'#','#','#','#','#','#','#');

    /* Copy chosen environment into env */
    short k=0;
    do
    :: k < N_CELLS -> env[k]=SRC[k]; k++
    :: else -> break
    od;

    /* Find start position */
    byte found=0; byte r=0; byte c=0;
    do
    :: (r<H && found==0) ->
         c=0;
         do
         :: (c<W && found==0) ->
              if
              :: (CELL(r,c)=='S') -> row=r; col=c; found=1; printf("Start found at (%d,%d)\n", r, c)
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
ltl no_wall        { [] !AT_WALL }
ltl door_a_closed  { [] ( AT_DOOR_A -> has_a ) }
ltl door_b_closed  { [] ( AT_DOOR_B -> has_b ) }
ltl door_c_closed  { [] ( AT_DOOR_C -> has_c ) }
ltl keep_a         { [] ( has_a -> X has_a ) }
ltl keep_b         { [] ( has_b -> X has_b ) }
ltl keep_c         { [] ( has_c -> X has_c ) }
ltl bounds_ok      { [] ( row < H && col < W ) }
ltl not_goal_reached { [] !goal_reached }
ltl reach_goal     { <> goal_reached }
ltl eventually_key_a { <> has_a }
ltl eventually_key_b { <> has_b }
ltl eventually_key_c { <> has_c }