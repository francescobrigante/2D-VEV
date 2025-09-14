/***********************
  * Virtual Environment Validator (1-D array version) - ROW/COL VERSION
  * Symbols:
  *  # wall, @ free, S start, G goal
  *  a,b,c keys <-> A,B,C doors
  ***********************/
#define W 35
#define H 35
#define N_CELLS (W*H)
#define SELECT_ENV 1  /* 1..3 */

/* Flattened environments */
byte env1[N_CELLS]; /* Correct */
byte env2[N_CELLS]; /* Unreachable Goal: walls */
byte env3[N_CELLS]; /* Unreachable Goal: key 'a' unreachable */
byte env[N_CELLS];  /* active environment */

/* Conversione 2D -> 1D */
#define IDX(row,col) ((row)*W + (col))
#define CELL(row,col) env[IDX(row,col)]

/* Macro per riempire una riga (row R) dell'ambiente E */
// #define SET_ROW(E,R,c0,c1,c2,c3,c4,c5,c6) \
//   E[IDX(R,0)]=c0; E[IDX(R,1)]=c1; E[IDX(R,2)]=c2; \
//   E[IDX(R,3)]=c3; E[IDX(R,4)]=c4; E[IDX(R,5)]=c5; E[IDX(R,6)]=c6

#define SET_ROW(E,R, c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c33,c34) \
  E[IDX(R,0)] = c0;   E[IDX(R,1)] = c1;   E[IDX(R,2)] = c2;   E[IDX(R,3)] = c3;   E[IDX(R,4)] = c4; \
  E[IDX(R,5)] = c5;   E[IDX(R,6)] = c6;   E[IDX(R,7)] = c7;   E[IDX(R,8)] = c8;   E[IDX(R,9)] = c9; \
  E[IDX(R,10)] = c10; E[IDX(R,11)] = c11; E[IDX(R,12)] = c12; E[IDX(R,13)] = c13; E[IDX(R,14)] = c14; \
  E[IDX(R,15)] = c15; E[IDX(R,16)] = c16; E[IDX(R,17)] = c17; E[IDX(R,18)] = c18; E[IDX(R,19)] = c19; \
  E[IDX(R,20)] = c20; E[IDX(R,21)] = c21; E[IDX(R,22)] = c22; E[IDX(R,23)] = c23; E[IDX(R,24)] = c24; \
  E[IDX(R,25)] = c25; E[IDX(R,26)] = c26; E[IDX(R,27)] = c27; E[IDX(R,28)] = c28; E[IDX(R,29)] = c29; \
  E[IDX(R,30)] = c30; E[IDX(R,31)] = c31; E[IDX(R,32)] = c32; E[IDX(R,33)] = c33; E[IDX(R,34)] = c34; \


/* Variabili di stato */
byte row=0;
byte col=0;
bit has_a=0, has_b=0, has_c=0;
bit goal_reached=0;
byte last_move=0;

/* Condizioni celle */
#define AT_WALL   (CELL(row,col)=='#')
#define AT_GOAL   (CELL(row,col)=='G')
#define AT_KEY_A  (CELL(row,col)=='a')
#define AT_KEY_B  (CELL(row,col)=='b')
#define AT_KEY_C  (CELL(row,col)=='c')
#define AT_DOOR_A (CELL(row,col)=='A')
#define AT_DOOR_B (CELL(row,col)=='B')
#define AT_DOOR_C (CELL(row,col)=='C')

/* Controllo se la cella è attraversabile */
#define PASSABLE(r,c) (CELL(r,c)!='#' && \
                      (CELL(r,c)!='A' || has_a) && \
                      (CELL(r,c)!='B' || has_b) && \
                      (CELL(r,c)!='C' || has_c))

/* Processo Robot */
proctype Robot() {
    int steps = 0;
    short visited[N_CELLS]; // matrice visitata 1D
    byte r, c;

    // Inizializza visited a 0
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

    // Aspetta posizione di start
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

        // Trova direzione meno visitata
        byte min_visit = 255;
        byte move_choice = 0;

        // Nord
        if
        :: (row>0 && PASSABLE(row-1,col)) ->
      //   :: (row>0 && PASSABLE(row-1,col) && last_move != 2) ->
            if
            :: visited[IDX(row-1,col)] < min_visit -> min_visit = visited[IDX(row-1,col)]; move_choice = 1
            :: else -> skip
            fi
        :: else -> skip
        fi;

        // Sud
        if
        :: (row<H-1 && PASSABLE(row+1,col)) ->
      //   :: (row<H-1 && PASSABLE(row+1,col) && last_move != 1) ->
            if
            :: visited[IDX(row+1,col)] < min_visit -> min_visit = visited[IDX(row+1,col)]; move_choice = 2
            :: else -> skip
            fi
        :: else -> skip
        fi;

        // Est
        if
        :: (col<W-1 && PASSABLE(row,col+1)) ->
      //   :: (col<W-1 && PASSABLE(row,col+1) && last_move != 4) ->
            if
            :: visited[IDX(row,col+1)] < min_visit -> min_visit = visited[IDX(row,col+1)]; move_choice = 3
            :: else -> skip
            fi
        :: else -> skip
        fi;

        // Ovest
        if
        :: (col>0 && PASSABLE(row,col-1)) ->
      //   :: (col>0 && PASSABLE(row,col-1) && last_move != 3) ->
            if
            :: visited[IDX(row,col-1)] < min_visit -> min_visit = visited[IDX(row,col-1)]; move_choice = 4
            :: else -> skip
            fi
        :: else -> skip
        fi;

        // Esegui mossa scelta
        if
        :: move_choice==1 -> printf("Chose North\n"); row = row-1; last_move = 1
        :: move_choice==2 -> printf("Chose South\n"); row = row+1; last_move = 2
        :: move_choice==3 -> printf("Chose East\n"); col = col+1; last_move = 3
        :: move_choice==4 -> printf("Chose West\n"); col = col-1; last_move = 4
        :: else -> printf("No valid moves, robot stuck\n"); break
        fi;

        printf("After move: at (%d,%d), cell='%c'\n", row, col, CELL(row,col));

        if :: (CELL(row,col)=='a') -> has_a=1; printf("Collected key a\n") :: else -> skip fi;
        if :: (CELL(row,col)=='b') -> has_b=1; printf("Collected key b\n") :: else -> skip fi;
        if :: (CELL(row,col)=='c') -> has_c=1; printf("Collected key c\n") :: else -> skip fi;

        steps++
    od;
}



/* Scelta ambiente */
#if SELECT_ENV==1
#define SRC env1
#elif SELECT_ENV==2
#define SRC env2
#elif SELECT_ENV==3
#define SRC env3
#else
#error "SELECT_ENV must be 1..3"
#endif

init {

   SET_ROW(env1,0,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,1,'@','S','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,2,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,3,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,4,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,5,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,6,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','A','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,7,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,8,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,9,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,10,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,11,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,12,'@','@','@','@','@','#','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,13,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,14,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,15,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,16,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','a','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,17,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','#','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,18,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,19,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,20,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,21,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,22,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,23,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,24,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,25,'@','@','@','@','@','@','@','#','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,26,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,27,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,28,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,29,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,30,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,31,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');
   SET_ROW(env1,32,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','#','#','#');
   SET_ROW(env1,33,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','#','G','@');
   SET_ROW(env1,34,'@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@','@');

  atomic {
    /* Copia ambiente scelto */
    short k=0;
    do
    :: k < N_CELLS -> env[k]=SRC[k]; k++
    :: else -> break
    od;

    /* Trova posizione start */
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