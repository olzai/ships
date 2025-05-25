/*
The game Ships is based on the package of `Simon Tatham's Portable Puzzle
Collection'. The aim of the game is to determine the positions of ships in a 
grid, given the sum totals of ship cells per row or column. 

Author: Oleg Zaitsev

Version 1, 20241030
Version 2, 20241224 (thanks to Simon Tatham for useful suggestions)
  1. A logical solver is implemented. Now the games with difficulty level <= 2
are guaranteed to be solvable without backtracking. The difficulty level is
now called "unreasonable".
  2. User interface is simplified: 
    (a) the user marks cells occupied or vacant, and the game fills 
the specific state of the cell; 
    (b) right drag marks multiple cells vacant or clears.
  3. For the field 7x7, 2 is now the minimum ship size (in version 1 it was 1).
  4. The code is optimized.
Version 3, 20250525
  Bug fixed: left drag is disabled.


Licence
-------

       This software is copyright 2025 Oleg Zaitsev.

       This software was developed using the package
       of `Simon Tatham's Portable Puzzle Collection'
       (www.chiark.greenend.org.uk/~sgtatham/puzzles). This software is
       _not_ part of the `Collection'.

       Permission is hereby granted, free of charge, to any person
       obtaining a copy of this software and associated documentation files
       (the `Software'), to deal in the Software without restriction,
       including without limitation the rights to use, copy, modify, merge,
       publish, distribute, sublicense, and/or sell copies of the Software,
       and to permit persons to whom the Software is furnished to do so,
       subject to the following conditions:

       The above copyright notice and this permission notice shall be
       included in all copies or substantial portions of the Software.

       THE SOFTWARE IS PROVIDED `AS IS', WITHOUT WARRANTY OF ANY KIND,
       EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
       OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
       NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
       BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
       ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
       CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
       SOFTWARE.

*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <ctype.h>
#ifdef NO_TGMATH_H
#  include <math.h>
#else
#  include <tgmath.h>
#endif

#include "puzzles.h"

/*-*-* colors */
enum {
    COL_BACKGROUND,
    COL_GRID,
    COL_GUESS = COL_GRID, 
    COL_SUMS = COL_GRID, 
    COL_SEGMENT = COL_GRID,
    COL_SHIPS = COL_GRID, 
    COL_OCCUP,
    COL_ERROR,
    COL_DONE_SUMS,
    COL_DONE_SHIPS = COL_DONE_SUMS,
    COL_HIGHLIGHT = COL_DONE_SUMS, 
    COL_DRAG = COL_DONE_SUMS, 
    COL_FLASH,
    NCOLOURS
};

/* ----------------------------------------------------------------------
 *-*-* my definitions
 */


/* Configuration of individual cells in the grid: 
  UNDEF  (-2): not disclosed/not yet known;
  VACANT (-1): not occupied; 
  OCCUP  (0):  occupied; 
  NORTH  (1):  North-directed ship end; 
  EAST   (2):  East-directed; 
  SOUTH  (3):  South-directed; 
  WEST   (4):  West-directed; 
  ONE    (5):  1-cell-ship;
  INNER  (6):  inner ship cell (not ship end).
*/
enum Configuration {
    UNDEF = -2,
    VACANT,
    OCCUP,
    NORTH,
    EAST,
    SOUTH,
    WEST,
    ONE,
    INNER
};


/* Difficulty levels */
enum Difficulty {
    BASIC,
    INTERMEDIATE,
    ADVANCED,
    UNREASONABLE
};


/* smallest, largest size */
#define SIZEMIN 7
#define SIZEMAX 25

/* solution returned by solver */
struct sol {
    // 2D array of the size num_ships x 3 array of ship coordinates 
    // (vert, y, x); vert = 0/1: horizontal/vertical; y,x: left top cell
    int **ship_coord;
    // possibly a second solution
    int **ship_coord2;
    // number of times the recursive function place_ship() was called. 
    // Used to estimate the complexity of the puzzle
    int count;
    // error value (0: no error/1: count_lim exceeded/2: non-unique solution
    // 3: no solution exist, when no limit set, i.e., count_lim <= 0)
    int err;
};


/* persistent elements in game state */
struct game_state_const {
    // count allocated states
    int refcount;
    // height, width, number of ships, sum of ship sizes, 
    // sum of rows/cols arrays (where > -1, see below)
    int H, W, num_ships, ships_sum, rows_sum, cols_sum;  
    // array of size num_ships of ship sizes (descending ordering)
    int *ships;
    // array of size ships[0]: ships_distr[i-1] is number of ships of size i
    int *ships_distr;
    // arrays of size H, W of row, column sums (-1 wenn missing)
    int *rows, *cols;
    // 2D-array of size H x W with the initial configuration
    int **init;    
};

/* comparison function for sorting (ctx = 1/-1: assending, descending) */
int cmp(const void *a, const void *b, void *ctx) {
   return (*((int*) a) - *((int*) b)) * (*((int*) ctx));
}

/* sizes that are relevant for drawing area size, as a function of tilesize */
#define BORDER_UP(x)     ((int) x/4)
#define BORDER_DOWN(x)   ((int) x/4)
#define BORDER_LEFT(x)   ((int) x/4)
#define BORDER_RIGHT(x)  ((int) x/2)
#define SUMS_UP(x)       (1*x)
#define SUMS_LEFT(x)     (1*x)
#define GRID_SPACE(x)    ((int) x/2)  // space under the grid
#define SHIPS(x)         ((int) 3*x/2) 

/* tile size on paper in mm (integer) */
#define TILE_SIZE_PAPER 9

/* completion flash */
#define FLASH_TIME 0.4F

/* condition for a corrupt string */
#define BADSTRING(p, atoi_p, pmin, pmax) *(p) && \
  (atoi_p < pmin || atoi_p > pmax - 1 || atoi_p == 0 && *(p) != '0') \
  || ! *(p)


/* matrix and its rotations */
#define MAT_0(i, j, m, h, w)  m[(i)][(j)]
#define MAT_1(i, j, m, h, w)  m[(j)][(h-1-(i))]  
#define MAT_2(i, j, m, h, w)  m[(h-1-(i))][w-1-(j)]            
#define MAT_3(i, j, m, h, w)  m[w-1-(j)][(i)]            
                      


/* ----------------------------------------------------------------------
 *-*-* end of my definitions
 */

/* ----------------------------------------------------------------------
 *-*-* headers of my functions that are specified at the end
 */
static void solver_init (const int h, const int w, int **init_ext);

static void solver (
  const struct game_state_const *init_state, int count_lim, struct sol *soln
);

static int solve_by_logic(
  int diff, const struct game_state_const *init_state, 
  enum Configuration **grid, int *occ, int *vac
);
 
static void render_grid_conf(
  int h, int w, enum Configuration **grid, enum Configuration **init, 
  bool remove
);

static void place_ship(
  const struct game_state_const *init_state, int **init_ext, bool ***blocked, 
  bool **ship_pos, int **ship_coord_tmp, int ship_num, int vert0, int y0, 
  int x0, int count_lim, struct sol *soln
);

static bool compl_ships_distr(
  int h, int w, int **grid, int max_size, int *distr
);

static void generator_diff(
  const game_params *params, random_state *rs, int *num_ships, int **ships, 
  int *rows, int *cols, int **init
);

static bool place_ship_rng(
  int ship_num, const game_params *params, int *ships, int *num_ships, 
  bool ***blocked, random_state *rs, int **ship_coord, int *count, 
  int count_lim
);
 
static void draw_segment(
  drawing *dr, const enum Configuration conf, const int tilesize, 
  const int xf, const int yf, const int color, const int color_bg
);

static void draw_cell(
  drawing *dr, const game_state *state, int xc, int yc, 
  int tilesize, int x0pt, int y0pt, bool cursor, bool error, bool update,
  bool drag, bool clear, enum Configuration conf, bool flash
);

static void validation(game_state *state, bool *solved);
/* ----------------------------------------------------------------------
 *-*-* end of headers 
 */



/*-*-* user controlled parameters for puzzle generation */
struct game_params {
    //-*-* height, width (>= SIZEMIN), difficulty (0 .. 3)
    int H, W;  
    enum Difficulty diff;
};


/*-*-* state saved on each step and accessed with undo/redo */
struct game_state { 
    //-*-* initially defined elements that do not change
    struct game_state_const *init_state;
    //-*-* 2D-array of size H x W with the current configuration 
    // as marked by user
    enum Configuration **grid_state;
    //-*-* arrays of size H, W of rows, cols marked as done by user
    bool *rows_state, *cols_state;
    //-*-* array of size init_state->num_ships; an element 
    // is true if the respective ship in the array init_state->ships is 
    // marked in the field (does not need to be the correct position)
    bool *ships_state;
    //-*-* 2D-array of size H x W; an element is true if the state 
    // of the cell is not consistent with its neighbors
    bool **grid_state_err;
    //-*-* arrays of size H, W; ; an element is true if the number 
    // of occupied cells in the row, column exceeds the required row 
    // or column sum
    bool *rows_err, *cols_err;
    //-*-* variable is true if the number of ships of some length
    // exceeds the required number of ships of this length
    bool ships_err;
    //-*-* flags showing if the game is solved and if cheated (solve function)
    bool completed, cheated;
};


/*-*-* default parameters */
static game_params *default_params(void)
{
    game_params *ret = snew(game_params);

    ret->H = 8;
    ret->W = 10;
    ret->diff = INTERMEDIATE;

    return ret;
}


static game_params *dup_params(const game_params *params)
{
    game_params *ret = snew(game_params);
    *ret = *params;		       /* structure copy */
    return ret;
}


/*-*-* parameters for preset menu "Type" */
static bool game_fetch_preset(int i, char **name, game_params **params)
{
    static struct {
        const char *title;
        game_params params;
    } const presets[] = {
        { "7x7 Basic",          {7, 7,   BASIC} },
        { "8x10 Basic",         {8, 10,  BASIC} },
        { "8x10 Intermediate",  {8, 10,  INTERMEDIATE} },
        { "8x10 Advanced",      {8, 10,  ADVANCED} },
        { "8x10 Unreasonable",  {8, 10,  UNREASONABLE} },
        { "10x12 Basic",        {10, 12, BASIC} },
        { "10x12 Intermediate", {10, 12, INTERMEDIATE} },
        { "10x12 Advanced",     {10, 12, ADVANCED} },
        { "10x12 Unreasonable", {10, 12, UNREASONABLE} },
    };

    if (i < 0 || i >= lenof(presets))
        return false;

    *name = dupstr(presets[i].title);
    *params = dup_params(&presets[i].params);

    return true;
}


static void free_params(game_params *params)
{
    sfree(params);
}


/*-*-* decode parameter substring in menu items Specific... 
and Random Seed...   */
static void decode_params(game_params *params, char const *string)
{
    //-*-* reset in order to cause validation error if not filled correctly
    params->H = -1;
    params->W = -1;
    
    //-*-* p will move along the string
    char const *p = string;
    
    if (*p && isdigit(*p)) params->H = atoi(p);
    else return;
    
    while (*p && isdigit(*p)) p++;
    
    if (*p && *p == 'x') p++;
    else return;
    
    if (*p && isdigit(*p)) params->W = atoi(p);
    else return;
    
    while (*p && isdigit(*p)) p++;
    
    //-*-* if difficulty is not specified in the form d{number}, the previous
    // is retained
    if (*p && *p == 'd') p++;
    else return;
    
    if (*p && isdigit(*p)) params->diff = atoi(p);
}


/*-*-* encode game parameters into string: "{H}x{W}" or "{H}x{W}d{diff}", 
the latter if full = true */
static char *encode_params(const game_params *params, bool full)
{
    char ret[128];
    sprintf(ret, "%dx%d", params->H, params->W);
    if (full) {
        sprintf(ret + strlen(ret), "d%d", params->diff);
    }
    return dupstr(ret);
}


/*-*-* define custom menu and initialize with current parameters */
static config_item *game_configure(const game_params *params)
{
    config_item *ret;
    char buf[64];

    ret = snewn(4, config_item);

    ret[0].name = "Height";
    ret[0].type = C_STRING;
    sprintf(buf, "%d", params->H);
    ret[0].u.string.sval = dupstr(buf);

    ret[1].name = "Width";
    ret[1].type = C_STRING;
    sprintf(buf, "%d", params->W);
    ret[1].u.string.sval = dupstr(buf);

    ret[2].name = "Difficulty";
    ret[2].type = C_CHOICES;
    sprintf(buf, ":Basic:Intermediate:Advanced:Unreasonable");
    ret[2].u.choices.choicenames = dupstr(buf);
    ret[2].u.choices.selected = params->diff;

    ret[3].name = NULL;
    ret[3].type = C_END;

    return ret;
}


/*-*-* read parameters from custom menu */
static game_params *custom_params(const config_item *cfg)
{
    game_params *ret = snew(game_params);

    ret->H = atoi(cfg[0].u.string.sval);
    ret->W = atoi(cfg[1].u.string.sval);
    ret->diff = cfg[2].u.choices.selected;

    return ret;
}



/*-*-* validate parameter substring */
static const char *validate_params(const game_params *params, bool full)
{    
    char s[256];
    
    if (full && (params->diff < 0 || params->diff > 3)) {    
        sprintf(s, "Unknown difficulty rating."); 
        return dupstr(s);
    } 
    
    else if (
      params->H < SIZEMIN || params->H > SIZEMAX || 
      params->W < SIZEMIN || params->W > SIZEMAX 
    ) 
    { 
        sprintf(s, 
          "Height and width must be between %d and %d.", SIZEMIN, SIZEMAX
        );
        return dupstr(s);
    }        
    
    return NULL;
}


/*-*-* generate game and create description string */
static char *new_game_desc(const game_params *params, random_state *rs,
			   char **aux, bool interactive)
{
    //-*-* game is generated in generator_diff(); here pointers for the
    // return data are defined and, where possible, nondynamically allocated;
    // the rest is allocated in the fuction
    int i, j;
    int h = params->H, w = params->W;
    int rows[h], cols[w];
    int num_ships, *ships;
    
    int *init[h], init_[h*w];
    for (i = 0; i < h; i++) {
        init[i] = init_ + i*w;
    }
    
    //-*-* generator
    generator_diff(params, rs, &num_ships, &ships, rows, cols, init);

    //-*-* define strings

    //-*-* string has the format as in following simplified example 
    // s5s5s4r11r0r-1r7r1c7c2c-1y0x11z-1y7x2z5, where s..s.. is
    // array ships, here [5,5,4], r..r.. is array rows, here 
    // [11,0,-1,7,1], c..c.. is array cols, here [7,2,-1], y..x..z..y..
    // is 2D-array of initially disclosed cells (not equal to -2), 
    // here [[0,11,-1],[7,2,5]]; its elements are [H-coord., W-coord., config.]
    
    //-*-* Max. length of the string: 
    // (num_ships + H + W)*3 + (# init > -2)*8 + 1
    // Calculate # init > -2
    int num_init = 0;
    for (i = 0; i < h*w; i++) {
        if (init_[i] > -2) num_init++;
    }
    
    //-*-* create string
    char *ret, *str;    
    str = snewn((num_ships + h + w)*3 + num_init*8 + 1, char); 
    ret = str; 
    
    for (i = 0; i < num_ships; i++) {
        sprintf(ret, "s%d", ships[i]);    
        ret += 2 + (ships[i] > 9); 
    }
    for (i = 0; i < h; i++) {
        sprintf(ret, "r%d", rows[i]);
        ret += 2 + (rows[i] < 0 || rows[i] > 9); 
    }
    for (i = 0; i < w; i++) {
        sprintf(ret, "c%d", cols[i]);
        ret += 2 + (cols[i] < 0 || cols[i] > 9); 
    }
    for (i = 0; i < h; i++) {
        for (j = 0; j < w; j++) {
            if (init[i][j] > -2) {
                sprintf(ret, "y%dx%dz%d", i, j, init[i][j]);
                ret += 6 + (i > 9) + (j > 9) + (init[i][j] < 0); 
            }
        }
    }
    
    ret = '\0';
        
    sfree(ships);
      
    return str;
}

/*-*-* validate game description */
static const char *validate_desc(const game_params *params, const char *desc)
{
    int 
      count_s = 0, count_r = 0, count_c = 0, count_y = 0, count_x = 0, 
      count_z = 0
    ;

    //-*-* p will move along the string
    char const *p = desc;
    int atoi_p;
    
    
    while (*p) {
    
        if (*p == 's') {
            count_s++;
            p++;
            atoi_p = atoi(p);
            if (*p &&  (atoi_p <= 0) || ! *p) {
                return "Positive integer expected after 's'.";
            }
            else if  (*p && (atoi_p > params->H || atoi_p > params->W)) {
                return "Ship size after 's' bigger than field size.";
            }
            else {
                while (*p && isdigit(*p)) p++;
            }
        }
        
        else if (*p == 'r') {
            count_r++;
            p++;
            atoi_p = atoi(p);
            if (BADSTRING(p, atoi_p, -1, params->W + 1)) {
                return "Integer between -1 and width is expected after 'r'.";
            }
            else {
                while (*p && isdigit(*p)) p++;
            }
        }
        
        else if (*p == 'c') {
            count_c++;
            p++;
            atoi_p = atoi(p);
            if (BADSTRING(p, atoi_p, -1, params->H + 1)) {
                return "Integer between -1 and height is expected after 'c'.";
            }
            else {
                while (*p && isdigit(*p)) p++;
            }
        }
        
        else if (*p == 'y') {
            count_y++;
            p++;
            atoi_p = atoi(p);
            if (BADSTRING(p, atoi_p, 0, params->H)) 
              return 
                "Integer between 0 and (height - 1) is expected after 'y'."
            ;
            else {
                while (*p && isdigit(*p)) p++;
            }
        }
        
        else if (*p == 'x') {
            count_x++;
            p++;
            atoi_p = atoi(p);
            if (BADSTRING(p, atoi_p, 0, params->W)) 
              return 
                "Integer between 0 and (width - 1) is expected after 'x'."
            ;
            else {
                while (*p && isdigit(*p)) p++;
            }
        }
        
        else if (*p == 'z') {
            count_z++;
            p++;
            atoi_p = atoi(p);
            if (BADSTRING(p, atoi_p, -1, 7)) {
                return "Integer between -1 and 6 is expected after 'z'.";
            }
            else {
                while (*p && isdigit(*p)) p++;
            }
        }
        
        else p++;
    
    }
    
    
    if (count_s < 1) {
        return "Number of ships 's' must be at least one.";
    }
    if (count_r != params->H) {
        return "Number of rows 'r' not equal to height.";
    }
    if (count_c != params->W) {
        return "Number of columns 'c' not equal to width.";
    }
    if (count_y != count_x || count_x != count_z) {
        return "Number of 'y', 'x', 'z' (coordinates and value of initially disclosed cells) must be equal.";
    }
    
    return NULL;
}


/*-*-* initial state (desc-string can have nonstandard ordering) */
static game_state *new_game(midend *me, const game_params *params,
                            const char *desc)
{
    int i, j;
    int h = params->H, w = params->W;

    game_state *state = snew(game_state);

    
    //-*-* initializations without using desc
    
    state->init_state = snew(struct game_state_const);
    state->init_state->refcount = 1;

    state->init_state->H = h;
    state->init_state->W = w;
    
    state->init_state->rows = snewn(h, int);
    state->init_state->cols = snewn(w, int);
    state->rows_state = snewn(h, bool);
    state->cols_state = snewn(w, bool);
    state->rows_err   = snewn(h, bool);
    state->cols_err   = snewn(w, bool);
    for (i = 0; i < h; i++) state->rows_state [i] = false;
    for (i = 0; i < w; i++) state->cols_state [i] = false;

    //-*-* 2D arrays
    state->init_state->init = snewn(h, int*);
    state->grid_state       = snewn(h, int*);
    state->grid_state_err   = snewn(h, bool*);
    *(state->init_state->init) = snewn(h*w, int); 
    *(state->grid_state)       = snewn(h*w, int); 
    *(state->grid_state_err)   = snewn(h*w, bool); 
    for (i = 1; i < h; i++) {
      state->init_state->init [i] = state->init_state->init [0] + i*w;
      state->grid_state [i]       = state->grid_state [0]       + i*w;
      state->grid_state_err [i]   = state->grid_state_err [0]   + i*w;
    }
    for (i = 0; i < h; i++) {
        for (j = 0; j < w; j++) {
            state->init_state->init [i][j] = -2;
            state->grid_state       [i][j] = -2;
        }
    }

    //-*-* initializations using desc

    //-*-* determine num_ships and number of initially disclosed cells
    char const *p = desc;
    int num_init = 0;
    state->init_state->num_ships = 0;
    while (*p) {    
        if      (*p == 's') (state->init_state->num_ships)++;
        else if (*p == 'y') num_init++;
        p++;
    }
    
    int ns = state->init_state->num_ships;
    state->init_state->ships = snewn(ns, int); 
    state->ships_state       = snewn(ns, bool); 
    
    //-*-* read from desc
    p = desc;
    int 
      count_s = 0, count_r = 0, count_c = 0, count_y = 0, count_x = 0,
      count_z = 0
    ;
    int y[num_init], x[num_init], z[num_init];
    
    while (*p) {    
        if (*p == 's') {
            p++;
            state->init_state->ships [count_s] = atoi(p);
            count_s++;
        }
        else if (*p == 'r') {
            p++;
            state->init_state->rows [count_r] = atoi(p);
            count_r++;
        }
        else if (*p == 'c') {
            p++;
            state->init_state->cols [count_c] = atoi(p);
            count_c++;
        }
        else if (*p == 'y') {
            p++;
            y[count_y] = atoi(p);
            count_y++;
        }
        else if (*p == 'x') {
            p++;
            x[count_x] = atoi(p);
            count_x++;
        }
        else if (*p == 'z') {
            p++;
            z[count_z] = atoi(p);
            count_z++;
        }
        else p++;   
    }
    
    //-*-* sums
    state->init_state->ships_sum = 0;
    for (i = 0; i < ns; i++) 
      state->init_state->ships_sum += state->init_state->ships[i]
    ;
    state->init_state->rows_sum = 0;
    for (i = 0; i < h; i++) {
      if (state->init_state->rows[i] > -1) 
        state->init_state->rows_sum += state->init_state->rows[i]
      ;
    }
    state->init_state->cols_sum = 0;
    for (i = 0; i < w; i++) {
      if (state->init_state->cols[i] > -1) 
        state->init_state->cols_sum += state->init_state->cols[i]
      ;
    }
    
    //-*-* fill initially disclosed cells (grid_state gets the same value)
    for (i = 0; i < num_init; i++){
        state->init_state->init  [y[i]] [x[i]] = z[i];
        state->grid_state        [y[i]] [x[i]] = z[i];
    }
    
    //-*-* specify type (1 to 6) of OCCUP cells wherever possible
    render_grid_conf(h, w, state->grid_state, state->init_state->init, false);

    //-*-* sort ships
    int ctx = -1;
    arraysort(state->init_state->ships, ns, cmp, &ctx);
        
    //-*-* ship distribution
    state->init_state->ships_distr = 
      snewn(state->init_state->ships [0], int)
    ;    
    for (i = 0; i < state->init_state->ships [0]; i++){
        state->init_state->ships_distr [i] = 0;
    }
    for (i = 0; i < ns; i++){
        (state->init_state->ships_distr [state->init_state->ships [i] - 1])++;
    }
        
    //-*-* check for errors
    bool solved; 
    validation(state, &solved);
    state->completed = solved;

    state->cheated   = false;
      
    return state;
}


/*-*-* copy of game state */
static game_state *dup_game(const game_state *state)
{
    game_state *ret = snew(game_state);
    
    int i;
    int h = state->init_state->H, w = state->init_state->W;
    int ns = state->init_state->num_ships;
    
    ret->ships_err = state->ships_err;
    ret->completed = state->completed;
    ret->cheated   = state->cheated;

    ret->grid_state    = snewn(h,   int*);
    *(ret->grid_state) = snewn(h*w, int); 
    for (i = 1; i < h; i++) {
        ret->grid_state [i] = ret->grid_state [0] + i*w;
    }
    memcpy(
      *(ret->grid_state), *(state->grid_state), 
      h*w*sizeof(**(ret->grid_state))
    );
    
    ret->grid_state_err    = snewn(h,   bool*);
    *(ret->grid_state_err) = snewn(h*w, bool); 
    for (i = 1; i < h; i++) {
        ret->grid_state_err [i] = ret->grid_state_err [0] + i*w;
    }
    memcpy(
      *(ret->grid_state_err), *(state->grid_state_err), 
      h*w*sizeof(**(ret->grid_state_err))
    );
    
    ret->rows_state = snewn(h,  bool);
    ret->cols_state = snewn(w,  bool);
    ret->rows_err   = snewn(h,  bool);
    ret->cols_err   = snewn(w,  bool);
    memcpy(ret->rows_state, state->rows_state, h*sizeof(*(ret->rows_state)));
    memcpy(ret->cols_state, state->cols_state, w*sizeof(*(ret->cols_state)));
    memcpy(ret->rows_err,   state->rows_err,   h*sizeof(*(ret->rows_err)));
    memcpy(ret->cols_err,   state->cols_err,   w*sizeof(*(ret->cols_err)));

    ret->ships_state = snewn(ns,  bool);
    memcpy(
      ret->ships_state, state->ships_state, ns*sizeof(*(ret->ships_state))
    );
    
    ret->init_state = state->init_state;
    ret->init_state->refcount++;
    
    return ret;
}


/*-*-* free game state */
static void free_game(game_state *state)
{
    sfree(*(state->grid_state));
    sfree(state->grid_state);
    sfree(*(state->grid_state_err));
    sfree(state->grid_state_err);
    
    sfree(state->rows_state);
    sfree(state->cols_state);
    sfree(state->rows_err);
    sfree(state->cols_err);
    
    sfree(state->ships_state);
    
    if (--state->init_state->refcount <= 0) {
        sfree(*(state->init_state->init));
        sfree(state->init_state->init);
        sfree(state->init_state->ships);
        sfree(state->init_state->ships_distr);
        sfree(state->init_state->rows);
        sfree(state->init_state->cols);
        sfree(state->init_state);
    }
        
    sfree(state);
}


/*-*-* yield solution (called when pressing Solve button) */
static char *solve_game(const game_state *state, const game_state *currstate,
                        const char *aux, const char **error)
{
    int i, j;
    int h = state->init_state->H, w = state->init_state->W;
    int ns = state->init_state->num_ships;
    int ships_sum = state->init_state->ships_sum;
    int *ships = state->init_state->ships;
    
    //-*-* define solution struct
    struct sol soln;
    soln.ship_coord  = snewn(ns, int*);
    soln.ship_coord2 = snewn(ns, int*);
    *(soln.ship_coord)  = snewn(ns*3, int);
    *(soln.ship_coord2) = snewn(ns*3, int);
    for (i = 1; i < ns; i++) {
        soln.ship_coord  [i] = soln.ship_coord  [0] + i*3;
        soln.ship_coord2 [i] = soln.ship_coord2 [0] + i*3;
    }
    
    solver (state->init_state, 0, &soln);
    
    if (soln.err == 2) { 
    	*error = "Multiple solutions exist for this puzzle";
	    return NULL; 
	}
    if (soln.err == 3) { 
    	*error = "No solution exists for this puzzle";
	    return NULL; 
	}
	
    char out[8*ships_sum + 2], *ptr = out;
    int vert, y, x, z;
    strcpy(ptr++, "S"); //-*-* first symbol S to indicate Solve usage
    for (i = 0; i < ns; i++) {
        for (j = 0; j < ships[i]; j++) {
            vert = soln.ship_coord[i][0];
            y    = soln.ship_coord[i][1] + j*vert;
            x    = soln.ship_coord[i][2] + j*(1 - vert);
            if      (ships[i] == 1)               z = ONE;
            else if (j == 0            &&   vert) z = NORTH;
            else if (j == 0            && ! vert) z = WEST;
            else if (j == ships[i] - 1 &&   vert) z = SOUTH;
            else if (j == ships[i] - 1 && ! vert) z = EAST;
            else                                  z = INNER;
            sprintf(ptr, "y%dx%dz%d", y, x, z);
            ptr += 6 + (y > 9) + (x > 9) + (z < 0);
        }
    }
    *ptr = '\0';
    
	sfree(*(soln.ship_coord));
	sfree(*(soln.ship_coord2));
	sfree(soln.ship_coord);
	sfree(soln.ship_coord2);
	
    return dupstr(out);

}


/*-*-* data not located in game_state */
struct game_ui {
    //-*-* drag start and end grid coords 
    int drag_sy, drag_sx, drag_ey, drag_ex; 
    //-*-* flag indicating if a drag is underway
    bool drag;
    //-*-* flag indicating if drag clears filled cells
    bool clear;
    //-*-* coordinates of the currently highlighted square on the grid
    int hy, hx;
    //-*-* flag indicating if the cursor is currently visible
    bool hshow;
};

static game_ui *new_ui(const game_state *state)
{
    game_ui *ui = snew(game_ui);
    ui->drag_sy = ui->drag_sx = ui->drag_ey = ui->drag_ex = -1;
    ui->drag = ui->clear = false;
    ui->hy = ui->hx = 0;
    ui->hshow = false;
    return ui;
}

static void free_ui(game_ui *ui)
{
    sfree(ui);
}


/*-*-* adjust game_ui after user actions 
  (not called if interpret_move() returns a special value)
*/
static void game_changed_state(game_ui *ui, const game_state *oldstate,
                               const game_state *newstate)
{
}


/*-*-* info needed for drawing that is not already in game_state */
struct game_drawstate {
    int tilesize;
    //-*-* coordinates of the upper left point of the grid frame
    int yg, xg;
    //-*-* coordinates of the upper left point of the first segment button
    // and distance to the upper left point of the next segment
    int ys, xs, dxs;
    //-*-* coordinates of the previously highlighted square on the grid
    int hy, hx;
    //-*-* flag indicating if the drawstate has changed after start
    bool started;
};


/*-*-* create move description string, adjust game_ui */
static char *interpret_move(const game_state *state, game_ui *ui,
                            const game_drawstate *ds,
                            int x, int y, int button)
{
    int h = state->init_state->H, w = state->init_state->W;  
    int ts = ds->tilesize, yg = ds->yg, xg = ds->xg; 
    int i, yy, xx;
    enum Configuration conf;
    enum Configuration **init = state->init_state->init;
    enum Configuration **grid = state->grid_state;
    char move[32];
    char *p;
    
    //-*-* are y, x within boundary?
    #define INGRID(y, x, yg, xg, h, w, ts) \
      yg <= y && y < yg + ts * h && xg <= x && x < xg + ts * w
      
    //-*-* find grid coordinates from mouse coordinates
    #define GRID_YX(yx, yxg, ts) (int) (yx - yxg) / ts
      
    //-*-* cursor moves
    if (IS_CURSOR_MOVE(button)) {
        p = move_cursor(button, &ui->hx, &ui->hy, w, h, false, &ui->hshow);
        return p;
    }
    
    //-*-* cursor after pressing Enter
    if (button == CURSOR_SELECT) {
        //-*-* new appearance
        if (! ui->hshow) {
            ui->hshow = true;
            return MOVE_UI_UPDATE;
        }
        //-*-* switch cell state
        else if (init[ui->hy][ui->hx] == UNDEF) {
            sprintf(
              move, "y%dx%dz%d", ui->hy, ui->hx, 
              (grid[ui->hy][ui->hx] + 3) % 3 - 2
            );
            return dupstr(move);
        }
    }

    
    
    //-*-* set VACANT with right click/drag
    
    //-*-* start a click/drag
    if (IS_MOUSE_DOWN(button) && button == RIGHT_BUTTON) {
        if (INGRID(y, x, yg, xg, h, w, ts)) {
        
            //-*-* hide cursor
            ui->hshow = false;
                
            yy = GRID_YX(y, yg, ts);  xx = GRID_YX(x, xg, ts);
            
            if (init[yy][xx] == UNDEF) {
                ui->drag_sy = ui->drag_ey = yy;
                ui->drag_sx = ui->drag_ex = xx;
        
                ui->drag = true;
        
                //-*-* draw or clear
                if (grid[yy][xx] == UNDEF) ui->clear = false;
                else                       ui->clear = true;
                return MOVE_UI_UPDATE;
            }
        }
        
        ui->drag_sy = ui->drag_sx = ui->drag_ey = ui->drag_ex = -1;
        return MOVE_UNUSED;
    }


    //-*-* the drag continues
    if (IS_MOUSE_DRAG(button) && ui->drag_sy != -1 && ui->drag_sx != -1) {
    
        ui->drag = false;
        
        //-*-* drag takes effect if strictly vertical or horizontal
        if (INGRID(y, x, yg, xg, h, w, ts)) {
        
            yy = GRID_YX(y, yg, ts);  xx = GRID_YX(x, xg, ts);
            
            if (yy == ui->drag_sy || xx == ui->drag_sx) {
                ui->drag_ey = yy;
                ui->drag_ex = xx;
                ui->drag = true;
            }
        }
        
        return MOVE_UI_UPDATE;
    }
    
    //-*-* the drag is finished
    if (IS_MOUSE_RELEASE(button) && ui->drag) {
        ui->drag = false;
        sprintf(move, "d%dy%dx%dy%dx%d", ui->clear, 
          ui->drag_sy, ui->drag_sx, ui->drag_ey, ui->drag_ex
        );
        ui->drag_sy = ui->drag_sx = ui->drag_ey = ui->drag_ex = -1;
        return dupstr(move);
    }
    
    
    //-*-* set row/column done
    if (button == LEFT_BUTTON) {
        //-*-* click row sum
        if (yg <= y && y < yg + ts*h && xg - SUMS_LEFT(ts) <= x && x < xg) {
            sprintf(move, "r%d", GRID_YX(y, yg, ts));
            return dupstr(move);
        }
        //-*-* click column sum
        if (yg - SUMS_UP(ts) <= y && y < yg && xg <= x && x < xg + ts*w) {
            sprintf(move, "c%d", GRID_YX(x, xg, ts));
            return dupstr(move);
        }
    } 
    
        
    //-*-* set state with left mouse click
    if (button == LEFT_BUTTON && INGRID(y, x, yg, xg, h, w, ts)) {
        yy = GRID_YX(y, yg, ts);  xx = GRID_YX(x, xg, ts);
        
       //-*-* hide cursor
        ui->hshow = false;
        
        //-*-* switch cell state
        if (init[yy][xx] == UNDEF) {
            if (grid[yy][xx] == UNDEF) conf = OCCUP;
            else                       conf = UNDEF;
            sprintf(move, "y%dx%dz%d", yy, xx, conf);
            return dupstr(move);
        }
    }
    
    return MOVE_UNUSED;
}


/*-*-* create game_state taking into account the move string */
static game_state *execute_move(const game_state *oldstate, const char *move)
{
    int h = oldstate->init_state->H, w = oldstate->init_state->W;  
    int ships_sum = oldstate->init_state->ships_sum;
    int sy[ships_sum], sx[ships_sum], sz[ships_sum]; 
    int isy = 0, isx = 0, isz = 0;
    int dy[2], dx[2], idx = 0, idy = 0;
    bool clear;
    int i, j;
	    
    int y = -10, x = -10, z = -10, r = -10, c = -10;	    
	char const *p = move;
	int atoi_p;
    while (*p) {
        if (*p == 'd') {
            p++;
            atoi_p = atoi(p);
            //-*-* validate for possibly corrupted load file
            if (BADSTRING(p, atoi_p, 0, 2)) return NULL;
            else {
                clear = atoi_p;
                while (*p && isdigit(*p)) p++;
            }
        }
        else if (*p == 'y') {
            p++;
            atoi_p = atoi(p);
            if (BADSTRING(p, atoi_p, 0, h)) return NULL;
            else {
                y = atoi_p;
                if (move[0] == 'S' && isy < ships_sum) sy[isy++] = y;
                if (move[0] == 'd' && idy < 2)         dy[idy++] = y;
                while (*p && isdigit(*p)) p++;
            }
        }
        else if (*p == 'x') {
            p++;
            atoi_p = atoi(p);
            if (BADSTRING(p, atoi_p, 0, w)) return NULL;
            else {
                x = atoi_p;
                if (move[0] == 'S' && isx < ships_sum) sx[isx++] = x;
                if (move[0] == 'd' && idx < 2)         dx[idx++] = x;
                while (*p && isdigit(*p)) p++;
            }
        }
        else if (*p == 'z') {
            p++;
            atoi_p = atoi(p);
            if (BADSTRING(p, atoi_p, -2, 7)) return NULL;
            else {
                z = atoi_p;
                if (move[0] == 'S' && isz < ships_sum) sz[isz++] = z;
                while (*p && isdigit(*p)) p++;
            }
        }
        else if (*p == 'r') {
            p++;
            atoi_p = atoi(p);
            if (BADSTRING(p, atoi_p, 0, h)) return NULL;
            else {
                r = atoi_p;
                while (*p && isdigit(*p)) p++;
            }
        }
        else if (*p == 'c') {
            p++;
            atoi_p = atoi(p);
            if (BADSTRING(p, atoi_p, 0, w)) return NULL;
            else {
                c = atoi_p;
                while (*p && isdigit(*p)) p++;
            }
        }
        else p++;
    }

    
    if (
      (y == -10 || x == -10 || z == -10 && move[0] != 'd') && 
      r == -10 && c == -10
    ) return NULL;
    

    game_state *state;
    state = dup_game(oldstate);
        
    //-*-* Solve button pressed
    if (move[0] == 'S') {
    
        if (isy < ships_sum || isx < ships_sum || isz < ships_sum)
          return NULL
        ;
    
	    memcpy(
	      *(state->grid_state), *(state->init_state->init),
	      sizeof(**(state->init_state->init))*h*w
	    );
	    
	    for (i = 0; i < ships_sum; i++) {
	        state->grid_state [sy[i]][sx[i]] = sz[i];
	    }
	    
		for (i = 0; i < h*w; i++) {
    		if ((*(state->grid_state)) [i] == UNDEF) 
    		  (*(state->grid_state)) [i] = VACANT
	    	;
		}
	        
	    state->cheated = true;	    
	}
	    
    //-*-* right drag/click
    else if (move[0] == 'd') {
    
        if (idy < 2 || idx < 2 || dy[0] != dy[1] && dx[0] != dx[1]) 
          return NULL
        ;
        
        for (i = min(dy[0], dy[1]); i <= max(dy[0], dy[1]); i++) {
            for (j = min(dx[0], dx[1]); j <= max(dx[0], dx[1]); j++) {
                if (
                  clear && state->init_state->init [i][j] == UNDEF &&
                   state->grid_state [i][j] == VACANT
                ) 
	              state->grid_state [i][j] = UNDEF
	            ;
	            if (! clear && state->grid_state [i][j] == UNDEF)
	              state->grid_state [i][j] = VACANT
	            ;
            }
        }
        
    }
    
    //-*-* single move
    else {
	    if (y != -10 && x != -10 && z != -10) {
	        if (state->init_state->init [y][x] == UNDEF) {
	            state->grid_state [y][x] = z;
	        }
	        else state->grid_state [y][x] = state->init_state->init [y][x];
	    }
	    else if (r != -10) state->rows_state[r] = ! oldstate->rows_state[r];
	    else               state->cols_state[c] = ! oldstate->cols_state[c];
	}
	
    //-*-* specify type (1 to 6) of OCCUP cells wherever possible
    render_grid_conf(h, w, state->grid_state, state->init_state->init, true);
    
	bool solved; 
	validation(state, &solved);
	state->completed |= solved;
	    	    
	return state;
}

/* ----------------------------------------------------------------------
 * Drawing routines.
 */

/*-*-* compute field size */
static void game_compute_size(const game_params *params, int tilesize,
                              const game_ui *ui, int *x, int *y)
{
    *y = 
      params->H * tilesize + 1 + BORDER_UP(tilesize) + BORDER_DOWN(tilesize) +
      SUMS_UP(tilesize) + GRID_SPACE(tilesize) + SHIPS(tilesize)
    ;     
    *x = 
      params->W * tilesize + 1 + BORDER_LEFT(tilesize) +
      BORDER_RIGHT(tilesize) + SUMS_LEFT(tilesize)
    ;	      
}


/*-*-* transmit tilesize to the game_drawstate */
static void game_set_size(drawing *dr, game_drawstate *ds,
                          const game_params *params, int tilesize)
{
    ds->tilesize = tilesize;
}


/*-*-* define colors in rgb format */
static float *game_colours(frontend *fe, int *ncolours)
{
    float *ret = snewn(3 * NCOLOURS, float);
    int i;

    frontend_default_colour(fe, &ret[COL_BACKGROUND * 3]);
    
    //-*-* correct background if too light or too dark; 
    // set COL_OCCUP, COL_DONE_SUMS, COL_FLASH
    for (i = 0; i < 3; i++) {
        if (ret[COL_BACKGROUND * 3 + i] < 0.7F) 
          ret[COL_BACKGROUND * 3 + i] = 0.7F
        ;
        else if (ret[COL_BACKGROUND * 3 + i] > 0.9F)
          ret[COL_BACKGROUND * 3 + i] = 0.9F
        ;
        ret[COL_OCCUP * 3 + i]     = 1.0F;
        ret[COL_DONE_SUMS * 3 + i] = 0.45F;
        ret[COL_FLASH * 3 + i]     = 0.42F;
    }
    
    ret[COL_GRID * 3 + 0]=0.0F;
    ret[COL_GRID * 3 + 1]=0.0F;
    ret[COL_GRID * 3 + 2]=0.0F;
    
    ret[COL_ERROR * 3 + 0]=1.0F;
    ret[COL_ERROR * 3 + 1]=0.0F;
    ret[COL_ERROR * 3 + 2]=0.0F;
    
    *ncolours = NCOLOURS;
    return ret;
}


static game_drawstate *game_new_drawstate(drawing *dr, const game_state *state)
{
    struct game_drawstate *ds = snew(struct game_drawstate);

    //-*-* receives the actual tilesize later via game_set_size()
    ds->started = false;

    return ds;
}

static void game_free_drawstate(drawing *dr, game_drawstate *ds)
{
    sfree(ds);
}



static void game_redraw(drawing *dr, game_drawstate *ds,
                        const game_state *oldstate, const game_state *state,
                        int dir, const game_ui *ui,
                        float animtime, float flashtime)
{
    int i, j;
    bool drag, flash = false;
    int h = state->init_state->H, w = state->init_state->W;  
    int ns = state->init_state->num_ships;
    int **init = state->init_state->init, **grid = state->grid_state;
    int ts = ds->tilesize;
    char text[16];
    
    //-*-* completion flash
    if (
      flashtime > 0 && (
        flashtime <= FLASH_TIME/3 || flashtime >= FLASH_TIME*2/3
      )
    ) flash = true;
    
    
    //-*-* size of field
    int y_pix, x_pix;
    game_params params;
    params.H = h; params.W = w; 
    game_compute_size(&params, ts, ui, &x_pix, &y_pix);
    
    //-*-* corners of the grid
    int y1 = BORDER_UP(ts) + SUMS_UP(ts);
    int x1 = BORDER_LEFT(ts) + SUMS_LEFT(ts); 
    int y2 = y1 + h*ts;
    int x2 = x1 + w*ts;
    //-*-* save for interpret_move(), game_get_cursor_location()
    ds->yg = y1;
    ds->xg = x1;
     
    
    //-*-* at (re-)start only (not changeable parts)
    if (!ds->started) {

        //-*-* background
        draw_rect(dr, 0, 0, x_pix, y_pix, COL_BACKGROUND);

        //-*-* grid
        for (i = 0; i <= h; i++) {
            draw_line(dr, x1, y1 + ts*i, x2, y1 + ts*i, COL_GRID);
        }
        for (i = 0; i <= w; i++) {
            draw_line(dr, x1 + ts*i, y1, x1 + ts*i, y2, COL_GRID);
        }
    
        //-*-* restore ds if restarted during the game (e.g., resizing)
        ds->hy = ui->hy;
        ds->hx = ui->hx;
        
	    ds->started = true;
    }
        
      
    //-*-* cursor moves only
    if (ui->hshow && ui->hy != ds->hy || ui->hx != ds->hx) {
            
        // redraw old
        i = ds->hy;
        j = ds->hx;
        draw_cell(
          dr, state, j, i, ts, x1, y1, false, 
          state->grid_state_err[i][j], true, false, false, -2, false
        );
    
        // redraw new
        i = ui->hy;
        j = ui->hx;
        draw_cell(
          dr, state, j, i, ts, x1, y1, true, 
          state->grid_state_err[i][j], true, false, false, -2, false
        );
        
        ds->hy = ui->hy;
        ds->hx = ui->hx;
    }
    
    //-*-* redraw at start or when cursor not moved
    else {
    
        //-*-* fill cells
        for (i = 0; i < h; i++) {
            for (j = 0; j < w; j++) {

                //-*-* show grey cell to change by drag
                drag = false;            
                if (ui->drag && init[i][j] == UNDEF  && 
                  min(ui->drag_sy, ui->drag_ey) <= i && 
                  i <= max(ui->drag_sy, ui->drag_ey) && 
                  min(ui->drag_sx, ui->drag_ex) <= j && 
                  j <= max(ui->drag_sx, ui->drag_ex) &&
                  (
                    ui->clear   && grid[i][j] == VACANT ||
                    ! ui->clear && grid[i][j] == UNDEF
                  )
                ) drag = true;
                
                draw_cell(
                  dr, state, j, i, ts, x1, y1, 
                  (i == ui->hy && j == ui->hx ? ui->hshow : false), 
                  state->grid_state_err[i][j], false, drag, ui->clear, 
                  VACANT, flash
                );                
            }
        }

    
        //-*-* sums
        
        //-*-* when color of characters changes, the old color can be 
        // seen at the edges; this is corrected by first placing 
        // a rectangle in background color 
        draw_rect(
          dr, x1 - SUMS_LEFT(ts), y1, SUMS_LEFT(ts), y2 - y1, COL_BACKGROUND
        );
        for (i = 0; i < h; i++) {
            if (state->init_state->rows[i] != -1) {
                sprintf(text, "%d", state->init_state->rows[i]);
                draw_text(
                  dr, x1 - SUMS_LEFT(ts)/4, y1 + ts/2 + ts*i, FONT_VARIABLE,
                  (ts > 30 ? ts*5/10 : ts*6/10), ALIGN_VCENTRE | ALIGN_HRIGHT,
                  (
                    state->rows_err[i] ? COL_ERROR : 
                    (state->rows_state[i] ? COL_DONE_SUMS : COL_SUMS)
                  ), 
                  text
                );
            }
        }
        //-*-* character edge correction
        draw_rect(
          dr, x1, y1 - SUMS_UP(ts), x2 - x1, SUMS_UP(ts), COL_BACKGROUND
        );
        for (i = 0; i < w; i++) {
            if (state->init_state->cols[i] != -1) {
                sprintf(text, "%d", state->init_state->cols[i]);
                draw_text(
                  dr, x1 + ts/2 + ts*i, y1 - SUMS_UP(ts)/4, FONT_VARIABLE,
                  (ts > 30 ? ts*5/10 : ts*6/10), ALIGN_VNORMAL | ALIGN_HCENTRE,
                  (
                    state->cols_err[i] ? COL_ERROR : 
                    (state->cols_state[i] ? COL_DONE_SUMS : COL_SUMS)
                  ), 
                  text
                );
            }
        }

    
        //-*-* ships
        
        //-*-* character edge correction
        draw_rect(
          dr, 0, y2 + GRID_SPACE (ts) + 1, x_pix, SHIPS(ts), COL_BACKGROUND
        );
        int dx_ships = 
          (x_pix - BORDER_LEFT(ts) - BORDER_RIGHT(ts)) / 
          (state->init_state->num_ships + 2)
        ;
        int y_ships = y2 + GRID_SPACE (ts) + SHIPS(ts)/2;
        sprintf(text, "ships:");
        draw_text(
          dr, BORDER_LEFT(ts) + dx_ships, y_ships, FONT_VARIABLE,
          min((dx_ships > 38 ? dx_ships*4/10 : dx_ships*6/10), 2*SHIPS(ts)/5), 
          ALIGN_VCENTRE | ALIGN_HCENTRE, COL_SHIPS, text
        );
        for (i = 0; i < state->init_state->num_ships; i++) {
            sprintf(text, "%d", (state->init_state->ships)[i]);
            draw_text(
              dr, BORDER_LEFT(ts) + dx_ships*(i + 2) + dx_ships/2, 
              y_ships, FONT_VARIABLE,
              min(
                (dx_ships > 38 ? dx_ships*4/10 : dx_ships*6/10), 2*SHIPS(ts)/5
              ), 
              ALIGN_VCENTRE | ALIGN_HCENTRE, 
              (
                 state->ships_err ? COL_ERROR : 
                 (state->ships_state[i] ? COL_DONE_SHIPS : COL_SHIPS)
              ), 
              text
            );
        }

        //-*-* redraw
        draw_update(dr, 0, 0, x_pix, y_pix);
    }    
}

static float game_anim_length(const game_state *oldstate,
                              const game_state *newstate, int dir, game_ui *ui)
{
    return 0.0F;
}


/*-*-* completion flash */
static float game_flash_length(
  const game_state *oldstate, const game_state *newstate, int dir, game_ui *ui
)
{
    if (!oldstate->completed && newstate->completed &&
	!oldstate->cheated && !newstate->cheated)
        return FLASH_TIME;
    return 0.0F;
}


static void game_get_cursor_location(const game_ui *ui,
                                     const game_drawstate *ds,
                                     const game_state *state,
                                     const game_params *params,
                                     int *x, int *y, int *w, int *h)
{
    if(ui->hshow) {
        *x = ds->xg + ui->hx * ds->tilesize;
        *y = ds->yg + ui->hy * ds->tilesize;
        *w = *h = ds->tilesize + 1;
    }
}


/*-*-* return 1 if completed, -1 if lost, 0 otherwise */
static int game_status(const game_state *state)
{
    if (state->cheated)        return -1;
    else if (state->completed) return 1;
    else                       return 0;
}


/*-*-* compute size on paper in mm */
static void game_print_size(const game_params *params, const game_ui *ui,
                            float *x, float *y)
{
    int pw, ph, ts = TILE_SIZE_PAPER*100;
    game_compute_size(params, ts, ui, &pw, &ph);
    *x = pw / 100.0F;
    *y = ph / 100.0F;  
}


/*-*-* prints the initial state of the game */
static void game_print(drawing *dr, const game_state *state, const game_ui *ui,
                       int tilesize)
{
    int ink = print_mono_colour(dr, 0);
    int i, j, ts = tilesize, shift;
    int h = state->init_state->H, w = state->init_state->W;  
    char text[16];

    //-*-* size of field
    int y_pix, x_pix;
    game_params params;
    params.H = h; params.W = w; 
    game_compute_size(&params, ts, ui, &x_pix, &y_pix);
    
    print_line_width(dr, ts/40);
    
    //-*-* corners of the grid 
    int y1 = BORDER_UP(ts) + SUMS_UP(ts);
    int x1 = BORDER_LEFT(ts) + SUMS_LEFT(ts); 
    int y2 = y1 + h*ts;
    int x2 = x1 + w*ts;
    
    //-*-* grid
    for (i = 0; i <= h; i++) {
        draw_line(dr, x1, y1 + ts*i, x2, y1 + ts*i, ink);
    }
    for (i = 0; i <= w; i++) {
        draw_line(dr, x1 + ts*i, y1, x1 + ts*i, y2, ink);
    }
        
    //-*-* fill cells
    shift = 3*ts/40;
    for (i = 0; i < h; i++) {
        for (j = 0; j < w; j++) {
            draw_segment(
              dr, state->grid_state[i][j], ts, x1 + ts*j, y1 + ts*i, ink, -1
            );
            //-*-* initially disclosed: double border
            if (state->init_state->init [i][j] > -2) {
                draw_rect_outline(
                  dr, x1 + ts*j + shift, y1 + ts*i + shift, ts - 2*shift, 
                  ts - 2*shift, ink
                );
            }
        }
    }
    
    //-*-* sums        
    for (i = 0; i < h; i++) {
        if (state->init_state->rows[i] != -1) {
            sprintf(text, "%d", state->init_state->rows[i]);
            draw_text(
              dr, x1 - SUMS_LEFT(ts)/4, y1 + ts/2 + ts*i, FONT_VARIABLE,
              (ts > 30 ? ts*5/10 : ts*6/10), ALIGN_VCENTRE | ALIGN_HRIGHT,
              ink, text
            );
        }
    }
    for (i = 0; i < w; i++) {
        if (state->init_state->cols[i] != -1) {
            sprintf(text, "%d", state->init_state->cols[i]);
            draw_text(
              dr, x1 + ts/2 + ts*i, y1 - SUMS_UP(ts)/4, FONT_VARIABLE,
              (ts > 30 ? ts*5/10 : ts*6/10), ALIGN_VNORMAL | ALIGN_HCENTRE,
              ink, text
            );
        }
    }
    
    //-*-* ships
    int dx_ships = 
      (x_pix - BORDER_LEFT(ts) - BORDER_RIGHT(ts)) / 
      (state->init_state->num_ships + 2)
    ;
    int y_ships = y2 + GRID_SPACE (ts) + SHIPS(ts)/2;
    sprintf(text, "ships:");
    draw_text(
      dr, BORDER_LEFT(ts) + dx_ships, y_ships, FONT_VARIABLE,
      min((dx_ships > 38 ? dx_ships*4/10 : dx_ships*6/10), 2*SHIPS(ts)/5), 
      ALIGN_VCENTRE | ALIGN_HCENTRE, ink, text
    );
    for (i = 0; i < state->init_state->num_ships; i++) {
        sprintf(text, "%d", (state->init_state->ships)[i]);
        draw_text(
          dr, BORDER_LEFT(ts) + dx_ships*(i + 2) + dx_ships/2, 
          y_ships, FONT_VARIABLE,
          min(
            (dx_ships > 38 ? dx_ships*4/10 : dx_ships*6/10), 2*SHIPS(ts)/5
          ), 
          ALIGN_VCENTRE | ALIGN_HCENTRE, ink, text
        );
    }
        
}


/*-*-* Generic name thegame changed into the specific name 
on platforms where all games are built in a single block */
#ifdef COMBINED
#define thegame ships /*-*-* changed from nullgame */
#endif

const struct game thegame = {
    "Ships", "games.ships", "ships",  /*-*-* changed from "Null Game", NULL, NULL */
    default_params,
    game_fetch_preset, NULL,
    decode_params,
    encode_params,
    free_params,
    dup_params,
    true, game_configure, custom_params, /*-*-* 1st value: can_configure */
    validate_params,
    new_game_desc,
    validate_desc,
    new_game,
    dup_game,
    free_game,
    true, solve_game, /* solve */
    false, NULL, NULL, /* can_format_as_text_now, text_format */
    NULL, NULL, /* get_prefs, set_prefs */
    new_ui,
    free_ui,
    NULL, /* encode_ui */
    NULL, /* decode_ui */
    NULL, /* game_request_keys */
    game_changed_state,
    NULL, /* current_key_label */
    interpret_move,
    execute_move,
    48 /*-*-* preferred_tilesize: changed from 20 */, game_compute_size, game_set_size,
    game_colours,
    game_new_drawstate,
    game_free_drawstate,
    game_redraw,
    game_anim_length,
    game_flash_length,
    game_get_cursor_location,
    game_status,
    true, false, /*-*-* can_print, can_print_in_colour */ game_print_size, game_print,
    false,			       /* wants_statusbar */
    false, NULL,                       /* timing_state */
    0,				       /* flags */
};


/* ----------------------------------------------------------------------
 *-*-* my functions
 */

/*
Enrich the init array using information that it provides

Parameters:
  h, w: height, width;
  **init_ext: 2D array of size h*w initialized with init array of game_state.

The function determines further information about the cells and writes it
into init_ext.

*/
static void solver_init(const int h, const int w, int **init_ext) 
{
    int i, j;
    
    for (i = 0; i < h; i++) {
        for (j = 0; j < w; j++) {
        
            // NORTH, SOUTH, EAST, WEST, e.g. in case of NORTH,
            // all neighbors except South blocked; South occupied
            #define CASE_NSEW(i, j, h, w, conf, mat, m)                      \
                if (mat((i), (j), m, h, w) == conf) {                        \
                    if (0 <= (i)-1) {                                        \
                        if (0 <= (j)-1) mat((i)-1, (j)-1, m, h, w) = VACANT; \
                        mat((i)-1, (j), m, h, w) = VACANT;                   \
                        if ((j)+1 < w)  mat((i)-1, (j)+1, m, h, w) = VACANT; \
                    }                                                        \
                    if (0 <= (j)-1) mat((i), (j)-1, m, h, w) = VACANT;       \
                    if ((j)+1 < w)  mat((i), (j)+1, m, h, w) = VACANT;       \
                    if ((i)+1 < h) {                                         \
                        if (0 <= (j)-1) mat((i)+1, (j)-1, m, h, w) = VACANT; \
                        mat((i)+1, (j), m, h, w) = max(                      \
                          mat((i)+1, (j), m, h,  w), OCCUP                   \
                        );                                                   \
                        if ((j)+1 < w) mat((i)+1, (j)+1, m, h, w) = VACANT;  \
                    }                                                        \
                }
            // apply the above with rotation symmetry transformations
            CASE_NSEW(i,     j,     h, w, NORTH, MAT_0, init_ext);  
            CASE_NSEW(w-1-j, i,     w, h, EAST,  MAT_1, init_ext);  
            CASE_NSEW(h-1-i, w-1-j, h, w, SOUTH, MAT_2, init_ext);   
            CASE_NSEW(j,     h-1-i, w, h, WEST,  MAT_3, init_ext);              
            #undef CASE_NSEW


            // ONE: all neighbors blocked
            if (init_ext[i][j] == ONE) { 
                if (0 <= i-1) {
                    if (0 <= j-1) init_ext[i-1][j-1] = VACANT;
                    init_ext[i-1][j] = VACANT;
                    if (j+1 < w)  init_ext[i-1][j+1] = VACANT;
                }
                if (0 <= j-1) init_ext[i][j-1] = VACANT;
                if (j+1 < w)  init_ext[i][j+1] = VACANT;
                if (i+1 < h) { 
                    if (0 <= j-1) init_ext[i+1][j-1] = VACANT;
                    init_ext[i+1][j] = VACANT;
                    if (j+1 < w)  init_ext[i+1][j+1] = VACANT;
                }
            }


            // INNER: diagonal neighbors blocked; if North or South
            // occupied (blocked), then East and West blocked (occupied)
            // and vice versa
            #define CASE_INNER(i, j, h, w, mat, m)                         \
                if (mat((i), (j), m, h, w) == INNER) {                     \
                    if (0 <= (i)-1 && 0 <= (j)-1)                          \
                      mat((i)-1, (j)-1, m, h, w) = VACANT                  \
                    ;                                                      \
                    if (0 <= (j)-1 && mat((i), (j)-1, m, h, w) >= 0) {     \
                        if (0 <= (i)-1) mat((i)-1, (j), m, h, w) = VACANT; \
                        if ((i)+1 < h)  mat((i)+1, (j), m, h, w) = VACANT; \
                    }                                                      \
                    else if (                                              \
                      (j) == 0 || mat((i), (j)-1, m, h, w) == VACANT       \
                    ) {                                                    \
                        if (0 <= (i)-1)                                    \
                          mat((i)-1, (j), m, h, w) = max(                  \
                            mat((i)-1, (j), m, h, w), OCCUP                \
                          )                                                \
                        ;                                                  \
                        if ((i)+1 < h)                                     \
                          mat((i)+1, (j), m, h, w) = max(                  \
                            mat((i)+1, (j), m, h, w), OCCUP                \
                          )                                                \
                        ;                                                  \
                    }                                                      \
                }
            CASE_INNER(i,     j,     h, w, MAT_0, init_ext);  
            CASE_INNER(w-1-j, i,     w, h, MAT_1, init_ext);  
            CASE_INNER(h-1-i, w-1-j, h, w, MAT_2, init_ext);   
            CASE_INNER(j,     h-1-i, w, h, MAT_3, init_ext);              
            #undef CASE_INNER
            
        }
    }


    // OCCUP: diagonal neighbors blocked (separate loop, because, in the
    // loop above, further cells can be labeled occupied)
    for (i = 0; i < h; i++) {
        for (j = 0; j < w; j++) {
            if (init_ext[i][j] == OCCUP) {
                if (0 <= i-1) {
                    if (0 <= j-1) init_ext[i-1][j-1] = VACANT;
                    if (j+1 < w)  init_ext[i-1][j+1] = VACANT;
                }
                if (i+1 < h) { 
                    if (0 <= j-1) init_ext[i+1][j-1] = VACANT;
                    if (j+1 < w)  init_ext[i+1][j+1] = VACANT;
                }
            }
        }
    }
            
}


/*
Solver

The procedure tries ship orientations and positions beginning with
the longest ship. The trial is performed by place_ship(), called for
the longest ship. If a position satisfies the conditions
given in the input arrays rows, cols and is compatible with the
initially disclosed cells, place_ship() calls itself with the second
longest ship, and so on. If a correct position of the smallest ship is
found, the solution is recorded and the search is continued in order
to check the uniqueness of the solution. 

Error codes:
  0: a unique solution is found;
  1: count_lim (see below) is exceeded, the search is interrupted;
  2: a second solution is found, the search is interrupted;
  3: no solution is found.

Parameters:
  *init_state: constant part of game_state (*ships_distr can be undefined);
  count_lim: maximum number of times the recursive function place_ship()
can be called, before the search is interrupted and an error returned; set 
to a value of 0 or less if no limit is desired;
  *soln: solution structure where the results are saved.
  
*/
static void solver(
  const struct game_state_const *init_state, int count_lim, struct sol *soln
)
{
    int i, k;
    int h = init_state->H, w = init_state->W;
    int ns = init_state->num_ships;
    int **init = init_state->init;

    // enrich the init array using information that it provides
    int *init_ext[h], init_ext_[h*w];
    for (i = 0; i < h; i++) {
        init_ext[i] = init_ext_ + i*w;
    }
    memcpy(init_ext_, *init, sizeof(**init)*h*w);
    solver_init(h, w, init_ext);

    // H x W field of ship positions
    bool *ship_pos[h], ship_pos_[h*w];
    for (i = 0; i < h; i++) ship_pos[i] = ship_pos_ + i*w;
    for (i = 0; i < h*w; i++) ship_pos_[i] = 0;
    
    // ns x 3 array of ship coordinates for currently tried positons;
    // they will be copied to soln->ship_coord for correct solution
    int *ship_coord_tmp[ns], ship_coord_tmp_[ns*3];
    for (k = 0; k < ns; k++) ship_coord_tmp[k] = ship_coord_tmp_ + k*3;

    // H x W layers of positions blocked by the 1st, 2nd, ... ships
    bool **blocked[ns-1], *blocked_[(ns-1)*h], blocked__[(ns-1)*h*w];
    for (k = 0; k < ns-1; k++) {
        blocked[k] = blocked_ + k*h;
        for (i = 0; i < h; i++) {
            blocked_[k*h+i] = blocked__ + (k*h+i)*w;
        }
    }
    for (k = 0; k < (ns-1)*h*w; k++) blocked__[k] = 0;

    soln->count = 0;
    soln->err = 3;  
    place_ship(
      init_state, init_ext, blocked, ship_pos, ship_coord_tmp, 0, 0, 0, 0, 
      count_lim, soln
    ); 

}


/*

Recursive procedure for the function solver() that tries possible
positions of a given ship. 

Parameters:
  *init_state: constant part of game_state (*ships_distr can be undefined);
  **init_ext: enriched 2D array of initially disclosed information produced by
solver_init();
  ***blocked: 3D array which consists of H x W layers of positions blocked by
the 1st, 2nd, ... ships;
  **ship_pos: H x W field of ship positions;
  **ship_coord_tmp: ns x 3 temporary array of ship coordinates analogous to 
soln->ship_coord (ns = number of ships);
  ship_num: current ship number 0, ..., ns-1;
  vert0, y0, x0: initial ship orientation and coordinates of upper left cell
at which the search is started (different from 0, 0, 0 if the ship 
ship_num-1 has the same size);
  count_lim: maximum number of times the recursive function place_ship()
can be called, before the search is interrupted and an error returned;
  *soln: solution structure where the results are saved.

*/
static void place_ship(
  const struct game_state_const *init_state, int **init_ext, bool ***blocked, 
  bool **ship_pos, int **ship_coord_tmp, int ship_num, int vert0, int y0, 
  int x0, int count_lim, struct sol *soln
)
{

    (soln->count)++;
    if (0 < count_lim && count_lim < soln->count) {
        soln->err = 1;
        return;
    }
    
    int i, j, k, sum, sum_hid, pos_No, vert0_new, y0_new, x0_new;
    bool brk, blk; // break/interrupt; cells were blocked
    int h = init_state->H, w = init_state->W;
    int ns = init_state->num_ships;
    int ships_sum = init_state->ships_sum;
    int rows_sum = init_state->rows_sum; 
    int cols_sum = init_state->cols_sum;
    int *rows = init_state->rows, *cols = init_state->cols;
    
    
    int ship = init_state->ships [ship_num];
    int vert, y, x, ship_H, ship_W, y_max, x_max;
    
    // ortientation 0: horiz.; 1: vertical (single orientation if ship = 1)
    for (vert = 0; vert < min(2, ship); vert++) {
    
        // ship dimensions
        ship_H = vert*ship + 1 - vert;
        ship_W = (1 - vert)*ship + vert;
        
        // left/top cell coordinates of the ship x, y max values (+1)
        y_max = h - ship_H + 1;
        x_max = w - ship_W + 1;
        for (y = 0; y < y_max; y++) {
            for (x = 0; x < x_max; x++) {
            
                // skip until the new initial position
                if (                                   
                  vert <  vert0                      ||                      
                  vert == vert0 && y <  y0           ||          
                  vert == vert0 && y == y0 && x < x0 
                ) continue;
                
                // check that ship ends are not placed on internal cells
                // or ship of size 1 not placed on UNDEF, OCCUP, or ONE
                if (
                  init_ext[y][x] == INNER                   || 
                  init_ext[y+ship_H-1][x+ship_W-1] == INNER ||
                  ship == 1 && ! (
                    init_ext[y][x] == UNDEF || init_ext[y][x] == OCCUP ||
                    init_ext[y][x] == ONE
                  )
                ) continue;
                
                // check that cells are not blocked
                brk = false;
                for (i = 0; i < ship_H; i++) {
                    for (j = 0; j < ship_W; j++) {
                        if (init_ext[y+i][x+j] == VACANT) {brk = true; break;}
                        for (k = 0; k < ship_num; k++) {
                            if (blocked[k][y+i][x+j]) {brk = true; break;}
                        }
                        if (brk) break;
                    }
                    if (brk) break;
                }
                if (brk) continue;
                
                // save position
                for (i = 0; i < ship_H; i++) {
                    for (j = 0; j < ship_W; j++) {
                        ship_pos[y+i][x+j] = 1;
                    }
                }
                ship_coord_tmp[ship_num][0] = vert;
                ship_coord_tmp[ship_num][1] = y;
                ship_coord_tmp[ship_num][2] = x;
                
                
                // not last ship
                if (ship_num < ns - 1) {
                
                    // check: sums of open and hidden rows/cols below limits
                    sum_hid = 0;
                    for (i = 0; i < h; i++) {
                        sum = 0;
                        if (rows[i] >= 0) {
                            for (j = 0; j < w; j++) sum += ship_pos[i][j];
                            if (sum > rows[i]) {brk = true; break;}
                        }
                        else {
                            for (j = 0; j < w; j++) sum_hid += ship_pos[i][j];
                        }
                    }
                    if (sum_hid > ships_sum - rows_sum) brk = true;
                    
                    if (! brk) {
                        sum_hid = 0;
                        for (j = 0; j < w; j++) {
                            sum = 0;
                            if (cols[j] >= 0) {
                                for (i = 0; i < h; i++) sum += ship_pos[i][j];
                                if (sum > cols[j]) {brk = true; break;}
                            }
                            else {
                                for (i = 0; i < h; i++) 
                                  sum_hid += ship_pos[i][j]
                                ;
                            }
                        }
                        if (sum_hid > ships_sum - cols_sum) brk = true;
                    }
                    
                    // block cells and further checks
                    blk = false;
                    if (! brk) {
                        blk = true;
                        
                        // block cells of and around the ship
                        for (i = max(y-1, 0); i < min(y + ship_H + 1, h); i++) 
                        {
                            for (
                              j = max(x-1, 0); j < min(x + ship_W + 1, w); j++
                            ) {
                                blocked[ship_num][i][j] = 1;
                            }
                        }
                    
                        // block rows/columns that are full
                        sum_hid = 0;
                        for (i = 0; i < h; i++) {
                            sum = 0;
                            if (rows[i] >= 0) {
                                for (j = 0; j < w; j++) sum += ship_pos[i][j];
                                if (sum == rows[i]) {
                                    for (j = 0; j < w; j++) 
                                      blocked[ship_num][i][j] = 1
                                    ;
                                }
                            }
                            else {
                                for (j = 0; j < w; j++) 
                                  sum_hid += ship_pos[i][j]
                                ;
                            }
                        }
                        if (sum_hid == ships_sum - rows_sum) {
                            for (i = 0; i < h; i++) {
                                if (rows[i] == -1) {
                                    for (j = 0; j < w; j++) 
                                      blocked[ship_num][i][j] = 1
                                    ;
                                }
                            }
                        }
                        
                        sum_hid = 0;
                        for (j = 0; j < w; j++) {
                            sum = 0;
                            if (cols[j] >= 0) {
                                for (i = 0; i < h; i++) sum += ship_pos[i][j];
                                if (sum == cols[j]) {
                                    for (i = 0; i < h; i++) 
                                      blocked[ship_num][i][j] = 1
                                    ;
                                }
                            }
                            else {
                                for (i = 0; i < h; i++) 
                                  sum_hid += ship_pos[i][j]
                                ;
                            }
                        }
                        if (sum_hid == ships_sum - cols_sum) {
                            for (j = 0; j < w; j++) {
                                if (cols[j] == -1) {
                                    for (i = 0; i < h; i++) 
                                      blocked[ship_num][i][j] = 1
                                    ;
                                }
                            }
                        }
                        
                        // check: blocked cells do not overlap with initially
                        // occupied
                        for (i = 0; i < h*w; i++) {
                            if (
                              (*(blocked[ship_num]))[i] && 
                              ! (*ship_pos)[i]          &&
                              ((*init_ext)[i] >= 0)
                            )  {brk = true; break;}
                        }
                    }
                    
                    // next ship
                    if (! brk) {
                        
                        // search start position: if same size, start after
                        // current ship
                        if (init_state->ships[ship_num + 1] == ship) {
                            pos_No = vert*h*w + y*w + x + 1;
                            vert0_new = (int) pos_No/(h*w);
                            y0_new = (int) (pos_No - vert0_new*h*w)/w;
                            x0_new = pos_No - vert0_new*h*w - y0_new*w;
                        }
                        else {
                            vert0_new = 0;
                            y0_new = 0;
                            x0_new = 0;
                        }
                        
                        // call recursively
                        place_ship(
                          init_state, init_ext, blocked, ship_pos, 
                          ship_coord_tmp, ship_num + 1, vert0_new, 
                          y0_new, x0_new, count_lim, soln
                        );
                        
                        if (soln->err == 1) return;
                    }
                    
                    // unblock cells before shifting ship position
                    if (blk) {
                        for (i = 0; i < h*w; i++) 
                          (*(blocked[ship_num]))[i] = 0
                        ;
                    }
                }
                
                
                // last ship
                else {
                
                    // final checks
                    
                    // check raw & column sums
                    for (i = 0; i < h; i++) {
                        sum = 0;
                        if (rows[i] >= 0) {
                            for (j = 0; j < w; j++) sum += ship_pos[i][j];
                            if (sum != rows[i]) {brk = true; break;}
                        }
                    }
                
                    if (! brk) {
                        for (j = 0; j < w; j++) {
                            sum = 0;
                            if (cols[j] >= 0) {
                                for (i = 0; i < h; i++) sum += ship_pos[i][j];
                                if (sum != cols[j]) {brk = true; break;}
                            }
                        }
                    }
                    
                    // check initial conditions
                    if (! brk) {
                        for (i = 0; i < h; i++) {
                            for (j = 0; j < w; j++) {
                        
                                // if init_ext >= 0, the cell is occupied
                                if (init_ext[i][j] >= 0 && ! ship_pos[i][j])
                                {brk = true; break;}
                                
                                switch (init_ext[i][j]) {
                                    // neighbor to the South occupied
                                    case NORTH:
                                        if (! ship_pos[i+1][j]) brk = true;
                                        break;
                                    case EAST:
                                        if (! ship_pos[i][j-1]) brk = true;
                                        break;
                                    case SOUTH:
                                        if (! ship_pos[i-1][j]) brk = true;
                                        break;
                                    case WEST:
                                        if (! ship_pos[i][j+1]) brk = true;
                                        break;
                                    // at least two neighbors occupied
                                    case INNER:
                                        if ( ! (
                                          i > 0   && ship_pos[i-1][j] &&
                                          i < h-1 && ship_pos[i+1][j]    ||
                                          j > 0   && ship_pos[i][j-1] &&
                                          j < w-1 && ship_pos[i][j+1]
                                        )) brk = true;
                                }
                                if (brk) break;
                            }
                            if (brk) break;
                        }
                    }
                    
                    // if checks OK, save solution; check uniqueness
                    if (! brk) {
                        if (soln->err == 3) {
                            memcpy(
                              *(soln->ship_coord), *ship_coord_tmp, 
                              ns*3*sizeof(**ship_coord_tmp)
                            );
                            soln->err = 0;
                        }
                        else {
                            memcpy(
                              *(soln->ship_coord2), *ship_coord_tmp, 
                              ns*3*sizeof(**ship_coord_tmp)
                            );
                            soln->err = 2;
                        }
                    }
                }
                
                
                // delete current position before shifting
                for (i = 0; i < ship_H; i++) {
                    for (j = 0; j < ship_W; j++) {
                        ship_pos[y+i][x+j] = 0;
                    }
                }
            
            }
        }        
    }
    
    return;
}



/*
Check if a solution using predefined logical strategies is possible.


Parameters:
  diff: difficulty level;
  *init_state: constant part of game_state (*ships_distr can be undefined);
  **grid: h x w array which will be filled with the information 
determined by the solver (completed or unfinished solution);
  *occ, *vac: points to the variable with number of occupied / vacant cells
found by the solver.

Returns 
  0: solution by simpler strategies is possible;
  1: solution is only is possible if applying more complex strategies in
addition to the simpler strategies;
  2: solution by the predefined strategies is not possible.

NB: Additional strategies are tried for diff > 1 only; for diff = 0, 1,
the function returns 0 or 2.

*/
static int solve_by_logic(
  int diff, const struct game_state_const *init_state, 
  enum Configuration **grid, int *occ, int *vac
) 
{
    int i, j, k, l, y, x; 
    int checksum, checksum_init, sum_occ1, sum_occ2, sum_und1, sum_und2;
    int h = init_state->H, w = init_state->W;
    int ns = init_state->num_ships;
    int *ships = init_state->ships;
    int **init = init_state->init;
    int ships_sum = init_state->ships_sum;
    int rows_sum = init_state->rows_sum; 
    int cols_sum = init_state->cols_sum;
    int *rows = init_state->rows, *cols = init_state->cols;
    int distr_all[ships[0]], distr_compl[ships[0]]; 
    int ship_min, ship_max, num_ship_max;
    int gap, num_gaps, num_full_gaps, ships_per_gap;
    
    // initialize array where the current configuration is kept
    memcpy(*grid, *init, sizeof(**init)*h*w);
    
    // check sum to determine whether grid was changed after 
    // applying the strategies
    checksum = 0;
    for (i = 0; i < h*w; i++) checksum += (*grid)[i]; 
    
    // distribution of ship lengths
    for (k = 0; k < ships[0]; k++) distr_all[k] = 0;
    for (i = 0; i < ns; i++) (distr_all[ships[i] - 1])++;
    

    // flags that switch additional strategies and indicate if they helped
    bool add_strat = false, complex_solve = false;
    
    // apply the strategies as long as they work
    do {      
        // mark cells next to occupied cells as occupied where possible;
        // mark cells around occupied cells vacant
        solver_init(h, w, grid);
        
        
        // try two strategies:
        // 1. if number of occupied cells of a row/column is equal to 
        // the sum total (incl. 0), mark the remaining cells vacant;
        // 2. if number of unmarked cells in a row/column is equal to 
        // the row/column sum minus occupied cells, mark the remaining 
        // cells occupied
        
        // rows
        sum_occ1 = sum_und1 = 0;
        for (i = 0; i < h; i++) {
            sum_occ2 = sum_und2 = 0;
            for (j = 0; j < w; j++) {
                if (grid[i][j] >= 0) {
                    if (rows[i] > -1) sum_occ2++;
                    else              sum_occ1++;
                }
                else if (grid[i][j] == UNDEF) {
                    if (rows[i] > -1) sum_und2++;
                    else              sum_und1++;
                }
            }
            if (sum_occ2 == rows[i]) {
                for (j = 0; j < w; j++) 
                  if (grid[i][j] == UNDEF) grid[i][j] = VACANT
                ;                    
            }
            else if (sum_und2 == rows[i] - sum_occ2) {
                for (j = 0; j < w; j++) 
                  if (grid[i][j] == UNDEF) grid[i][j] = OCCUP
                ;                    
            }
        }
        // rows with hidden sum total
        if (sum_occ1 == ships_sum - rows_sum) {
            for (i = 0; i < h; i++) {
                if (rows[i] == -1) {
                    for (j = 0; j < w; j++) 
                      if (grid[i][j] == UNDEF) grid[i][j] = VACANT
                    ;
                }
            }
        }        
        else if (sum_und1 == ships_sum - rows_sum - sum_occ1) {
            for (i = 0; i < h; i++) {
                if (rows[i] == -1) {
                    for (j = 0; j < w; j++) 
                      if (grid[i][j] == UNDEF) grid[i][j] = OCCUP
                    ;
                }
            }
        }        
        // columns
        sum_occ1 = sum_und1 = 0;
        for (j = 0; j < w; j++) {
            sum_occ2 = sum_und2 = 0;
            for (i = 0; i < h; i++) {
                if (grid[i][j] >= 0) {
                    if (cols[j] > -1) sum_occ2++;
                    else              sum_occ1++;
                }
                else if (grid[i][j] == UNDEF) {
                    if (cols[j] > -1) sum_und2++;
                    else              sum_und1++;
                }
            }
            if (sum_occ2 == cols[j]) {
                for (i = 0; i < h; i++) 
                  if (grid[i][j] == UNDEF) grid[i][j] = VACANT
                ;                    
            }
            else if (sum_und2 == cols[j] - sum_occ2) {
                for (i = 0; i < h; i++) 
                  if (grid[i][j] == UNDEF) grid[i][j] = OCCUP
                ;                    
            }
        }
        // columns with hidden sum total
        if (sum_occ1 == ships_sum - cols_sum) {
            for (j = 0; j < w; j++) {
                if (cols[j] == -1) {
                    for (i = 0; i < h; i++) 
                      if (grid[i][j] == UNDEF) grid[i][j] = VACANT
                    ;
                }
            }
        }
        else if (sum_und1 == ships_sum - cols_sum - sum_occ1) {
            for (j = 0; j < w; j++) {
                if (cols[j] == -1) {
                    for (i = 0; i < h; i++) 
                      if (grid[i][j] == UNDEF) grid[i][j] = OCCUP
                    ;
                }
            }
        }        
        
        
        // 3. if a stripe of occupied cells is of the size of 
        // the longest unfinished ship, mark the cells next to the
        // end cells vacant
        
        // specify the type of occupied cells
        render_grid_conf(h, w, grid, init, false);
        
        // determine the longest unfinished ship size and their number;
        compl_ships_distr(h, w, grid, ships[0], distr_compl);
        ship_max = 0;
        for (i = ships[0] - 1; i >= 0; i--) {
            if (distr_compl[i] < distr_all[i]) {
                ship_max = i + 1; 
                break;
            }
        }
        
        // find stripes of occupied cells
        // rows
        for (i = 0; i < h; i++) {
            k = 1;
            for (j = 0; j < w; j++) {
                if (grid[i][j] >= 0) {
                    if (k < ship_max) k++;
                    else if (
                      ship_max > 1 ||
                      (i == 0   || grid[i-1][j] < 0) &&
                      (i == h-1 || grid[i+1][j] < 0) 
                    ) {
                        if (j < w-1 && grid[i][j+1] == UNDEF) 
                          grid[i][j+1] = VACANT
                        ;
                        if (j-k >= 0 && grid[i][j-k] == UNDEF) 
                          grid[i][j-k] = VACANT
                        ;
                    }
                }
                
                else k = 1;
            }
        }
        // columns
        for (j = 0; j < w; j++) {
            k = 1;
            for (i = 0; i < h; i++) {
                if (grid[i][j] >= 0) {
                    if (k < ship_max) k++;
                    else if (
                      ship_max > 1 ||
                      (j == 0   || grid[i][j-1] < 0) &&
                      (j == w-1 || grid[i][j+1] < 0) 
                    ) {
                        if (i < h-1 && grid[i+1][j] == UNDEF) 
                          grid[i+1][j] = VACANT
                        ;
                        if (i-k >= 0 && grid[i-k][j] == UNDEF) 
                          grid[i-k][j] = VACANT
                        ;
                    }
                }
                
                else k = 1;
            }
        }

       
        // initial check sum
        checksum_init = checksum;
        
        // check if configuration has changed
        checksum = 0;
        for (i = 0; i < h*w; i++) checksum += (*grid)[i];
        
        // apply additional strategies for a higher difficulty if
        // the simpler strategies no longer work
        if (diff > 1) {
            // turn on/off additional strategies
            if (checksum == checksum_init) add_strat = ! add_strat;
            // record if additional strategies caused to 
            // change the check sum at least once
            else if (add_strat) complex_solve = true;
        }
        if (diff > 1 && add_strat) {
            // specify the type of occupied cells
            render_grid_conf(h, w, grid, init, false);
            
            
            // 4. mark cells vacant where the available gaps are shorter
            // than the shortest unfinished ship
            
            // determine the shortest unfinished ship
            compl_ships_distr(h, w, grid, ships[0], distr_compl);
            ship_min = 0;
            for (i = 0; i < ships[0]; i++) {
                if (distr_compl[i] < distr_all[i]) {
                    ship_min = i + 1; break;
                }
            }

            // determine the gaps
            for (i = 0; i < h; i++) {for (j = 0; j < w; j++) {
                if (grid[i][j] == UNDEF) {
                    // go down
                    k = 1;
                    while (
                      k < ship_min && i+k < h && grid[i+k][j] != VACANT
                    ) k++;
                    gap = k;
                    if (gap >= ship_min) continue;
                    // go up
                    k = 1;
                    while (
                      gap+k-1 < ship_min && i-k >= 0 && grid[i-k][j] != VACANT 
                    ) k++;
                    gap += k-1;
                    if (gap >= ship_min) continue;
                    // go right
                    k = 1;
                    while (
                      k < ship_min && j+k < w && grid[i][j+k] != VACANT 
                    ) k++;
                    gap = k;
                    if (gap >= ship_min) continue;
                    // go left
                    k = 1;
                    while (
                      gap+k-1 < ship_min && j-k >= 0 && grid[i][j-k] != VACANT 
                    ) k++;
                    gap += k-1;
                    if (gap < ship_min) grid[i][j] = VACANT;
                }
            }}
            

            // 5. Determine the number of gaps where the longest 
            // unfinished ship would fit. Exclude rows and columns
            // with sum totals smaller than the longest unfinished ship.
            // If number of gaps is equal to the number of longest 
            // unfinished ships, fill the gaps as much as possible.

            // determine the longest unfinished ship size and their number;
            // no need for compl_ships_distr(), because strategy No. 4
            // cannot generate new completed ships
            ship_max = num_ship_max = 0;
            for (i = ships[0] - 1; i >= 0; i--) {
                if (distr_compl[i] < distr_all[i]) {
                    ship_max = i + 1; 
                    num_ship_max = distr_all[i] - distr_compl[i];
                    break;
                }
            }
            if (ship_max == 1) continue; // more complex logic, won't consider
            
            // array to record the gaps; per gap, vert (0/1), y, x, length 
            int gaps[num_ship_max*4];
            
            // determine the number of gaps (conservatively, the upper 
            // boundary)
            num_gaps = 0; // count more than once if more than one ships fit
            num_full_gaps = 0; // count each gap once (capped by num_ship_max)
            // rows
            for (i = 0; i < h; i++) { 
                if (
                  rows[i] >= ship_max || 
                  rows[i] == -1 && ships_sum - rows_sum >= ship_max
                ) {
                    for (j = 0; j < w; j++) {
                        if (grid[i][j] == UNDEF) {
                            // go left
                            k = 1;
                            while (j-k >= 0 && grid[i][j-k] != VACANT) k++;
                            gap = k;
                            // go right
                            k = 1;
                            while (j+k < w && grid[i][j+k] != VACANT) k++;
                            gap += k-1;
                            // record
                            if (
                              gap >= ship_max && num_full_gaps < num_ship_max
                            ) {
                                gaps[num_full_gaps*4    ] = 0;
                                gaps[num_full_gaps*4 + 1] = i;
                                gaps[num_full_gaps*4 + 2] = j + k - gap;
                                gaps[num_full_gaps*4 + 3] = gap;
                                num_full_gaps++;
                            }
                            // upper bound
                            num_gaps += (int) (gap + 1)/(ship_max + 1); 
                            // shift to the end of gap
                            j += k-1;
                        }
                    }
                }
            }
            // columns
            for (j = 0; j < w; j++) {
                if (
                  cols[j] >= ship_max || 
                  cols[j] == -1 && ships_sum - cols_sum >= ship_max
                ) {
                    for (i = 0; i < h; i++) {
                        if (grid[i][j] == UNDEF) {
                            // go up
                            k = 1;
                            while (i-k >= 0 && grid[i-k][j] != VACANT) k++;
                            gap = k;
                            // go down
                            k = 1;
                            while (i+k < h && grid[i+k][j] != VACANT) k++;
                            gap += k-1;
                            if (
                              gap >= ship_max && num_full_gaps < num_ship_max
                            ) {
                                gaps[num_full_gaps*4    ] = 1;
                                gaps[num_full_gaps*4 + 1] = i + k - gap;
                                gaps[num_full_gaps*4 + 2] = j;
                                gaps[num_full_gaps*4 + 3] = gap;
                                num_full_gaps++;
                            }
                            num_gaps += (int) (gap + 1)/(ship_max + 1);
                            i += k-1;
                        }
                    }
                }
            }
            
            // fill the gaps (as in a nonogram)
            if (num_gaps == num_ship_max) {
                for (i = 0; i < num_full_gaps; i++) {
                    k = (gaps[i*4 + 3] + 1) % (ship_max + 1);
                    ships_per_gap = (int) (gaps[i*4 + 3] + 1)/(ship_max + 1);
                    for (j = 0; j < ships_per_gap; j++) {
                        for (l = 0; l < ship_max; l++) {
                            y = gaps[i*4+1] + gaps[i*4]*(j*(ship_max+1) + l);
                            x = 
                              gaps[i*4+2] + (1-gaps[i*4])*(j*(ship_max+1) + l)
                            ;
                            if (l >= k && grid[y][x] == UNDEF) 
                              grid[y][x] = OCCUP
                            ;
                        }
                    }
                }
            }
                        
        }
        
    } while (checksum != checksum_init || add_strat);
    
    // count occupied / vacant cells found
    *occ = *vac = 0;
    for (i = 0; i < h*w; i++) {
        *occ += ((*grid)[i] >= 0);
        *vac += ((*grid)[i] == -1);
    }
    
    // check if all occupied cells were found
    if (*occ == ships_sum) {
        if (diff <= 1 || ! complex_solve) return 0;
        else                              return 1;
    }
    else                                  return 2;
}




/*
Where possible, change cell state OCCUP to a specific state 1 to 6, and back.

Parameters:
  h, w: height, width of the grid;
  **grid: 2D array of size H x W of grid configuration;
  **init: 2D array of size H x W of initial grid configuration 
(disregarded if remove == false);
  remove: if true, the value of the cell will be set back to OCCUP, if not
uniquely defined and not fixed by the init array; if false, the value 
can only be promoted from OCCUP to 1..6.

*/
static void render_grid_conf(
  int h, int w, enum Configuration **grid, enum Configuration **init, 
  bool remove
)
{
    int i, j;
    enum Configuration **g = grid;

    for (i = 0; i < h; i++) {
        for (j = 0; j < w; j++) {
            if (g[i][j] == OCCUP) {
            
                // set OCCUP to 1..6
                if (
                  (i == 0 || g[i-1][j] == VACANT) && i < h-1 && g[i+1][j] >= 0
                ) g[i][j] = NORTH;
                
                else if (
                  (i == h-1 || g[i+1][j] == VACANT) && i > 0 && g[i-1][j] >= 0
                ) g[i][j] = SOUTH;
                
                else if (
                  (j == 0 || g[i][j-1] == VACANT) && j < w-1 && g[i][j+1] >= 0
                ) g[i][j] = WEST;
                
                else if (
                  (j == w-1 || g[i][j+1] == VACANT) && j > 0 && g[i][j-1] >= 0
                ) g[i][j] = EAST;              
                
                else if (
                  (i == 0   || g[i-1][j] == VACANT) && 
                  (i == h-1 || g[i+1][j] == VACANT) &&
                  (j == 0   || g[i][j-1] == VACANT) &&
                  (j == w-1 || g[i][j+1] == VACANT) 
                ) g[i][j] = ONE;              
                
                else if (
                  i > 0 && g[i-1][j] >= 0 && i < h-1 && g[i+1][j] >= 0 ||
                  j > 0 && g[i][j-1] >= 0 && j < w-1 && g[i][j+1] >= 0
                ) g[i][j] = INNER;   
                         
            }
           
            
            // set back to OCCUP
            else if (remove && g[i][j] > 0 && init[i][j] <= 0 && 
              (
                g[i][j] == NORTH && 
                (i > 0 && g[i-1][j] != VACANT || g[i+1][j] < 0)
                ||
                g[i][j] == SOUTH && 
                (i < h-1 && g[i+1][j] != VACANT || g[i-1][j] < 0)
                || 
                g[i][j] == WEST && 
                (j > 0 && g[i][j-1] != VACANT || g[i][j+1] < 0)
                ||
                g[i][j] == EAST && 
                (j < w-1 && g[i][j+1] != VACANT || g[i][j-1] < 0)
                ||
                g[i][j] == ONE && ! (
                  (i == 0   || g[i-1][j] == VACANT) &&
                  (i == h-1 || g[i+1][j] == VACANT) &&
                  (j == 0   || g[i][j-1] == VACANT) &&
                  (j == w-1 || g[i][j+1] == VACANT) 
                )
                ||
                g[i][j] == INNER && ! (
                  i > 0 && g[i-1][j] >= 0 && i < h-1 && g[i+1][j] >= 0 ||
                  j > 0 && g[i][j-1] >= 0 && j < w-1 && g[i][j+1] >= 0
                )
              )
            ) g[i][j] = OCCUP;
           
        }
    }
    
    
}



/*
Search for completed ships and determine their size distribution.

Parameters:
  h, w: height, width of the grid;
  **grid: 2D array of size H x W of grid configuration;
  max_size: the largest ship searched for (given by ships[0], the 0th element
of the array of ship lengths); larger completed ships will be ignored;
  *distr: array of size max_size of size distribution; in distr[i] the
number of completed ships of length i+1 will be saved.

The function returns "true" (error) if max_size is exceeded, otherwise 
"false".

*/
static bool compl_ships_distr(
  int h, int w, int **grid, int max_size, int *distr
)
{
    int i, j, k;
    bool err = false;
    int **g = grid;
    
    for (k = 0; k < max_size; k++) distr[k] = 0;
    
    // determine completed ships that start with NORTH
    // or WEST and end with SOUTH or EAST, also ONE-ships
    for (i = 0; i < h; i++) {
        for (j = 0; j < w; j++) {
        
            if (i < h-1 && g[i][j] == NORTH) {
                k = 0;
                do {k++;} 
                  while (i+k < h-1 && g[i+k][j] == INNER && k < max_size-1)
                ; 
                if (g[i+k][j] == SOUTH) (distr[k])++;
                else if (g[i+k][j] == INNER) err = true;
            }
            
            else if (j < w-1 && g[i][j] == WEST) {
                k = 0;
                do {k++;} 
                  while (j+k < w-1 && g[i][j+k] == INNER && k < max_size-1)
                ; 
                if (g[i][j+k] == EAST) (distr[k])++;
                else if (g[i][j+k] == INNER) err = true;
            }
            
            else if (g[i][j] == ONE) (distr[0])++;
            
        }
    }
    
    return err;
}



/*
Generate puzzle with given difficulty. 

Parameters:
  *params: game parameters;
  *rs: random state;
  *num_ships: pointer under which the generated number of ships will be saved;
  **ships: array of size *num_ships where ship sizes will be saved (sorted in
descending order);
  *rows, *cols: arrays of sizes H, W, resp., where the row and column sums 
will be saved;
  **init: 2D array of size H x W where the initially disclosed information
for the grid will be saved.

*/
static void generator_diff(
  const game_params *params, random_state *rs, int *num_ships, int **ships,
  int *rows, int *cols, enum Configuration **init
)
{
    int i, j, k, ship_ex, change, ex, num_init, num_wrong, log_solve;
    bool err, flag_break;
    int h = params->H, w = params->W, diff = params->diff;
    int *ns = num_ships;
        
        
    //****** determine ships
    
    if (min(h, w) == 7) {
        *ns = 7;  
        *ships = snewn(*ns, int);
        (*ships)[0] = (*ships)[1] = 4;
        (*ships)[2] = (*ships)[3] = 3;
        (*ships)[4] = (*ships)[5] = (*ships)[6] = 2;
    }
    else {
        // number of ships 7 or 8
        if (diff == BASIC) *ns = 7;
        else               *ns = 7 + random_upto(rs, 2);
        *ships = snewn(*ns, int);
        // maximal ship size
        int ship_max = round(min(h, w)*.6);
        // divide ship sizes in 4 groups; pick 2 sizes from each group
        // (if 7 ships then one size from the lowest group)
        float group_size = (ship_max - 1)/3.9999F; 
        // not integer! divisor slightly shifted from 4.0 for stability
                
        // if difficulty <= INTERMEDIATE then pick the biggest size from
        // 1st group (small ships are more difficult to find)
        if (diff <= INTERMEDIATE) {
            (*ships)[6]     = (int) group_size + 1;
            (*ships)[*ns-1] = (*ships)[6];
        }
        else {
            (*ships)[6]     = 1 + random_upto(rs, (int) group_size + 1);
            (*ships)[*ns-1] = 1 + random_upto(rs, (int) group_size + 1);
        }
        
        // 2nd, 3rd, 4th groups
        for (i = 0; i < 3; i++) {
            (*ships)[i*2] = 
              ((int) group_size*(i+1)) + 2 +
              random_upto(
                rs, ((int) group_size*(i+2)) - ((int) group_size*(i+1)) 
              )
            ;
            (*ships)[i*2+1] = 
              ((int) group_size*(i+1)) + 2 + 
              random_upto(
                rs, ((int) group_size*(i+2)) - ((int) group_size*(i+1)) 
              )
            ;
        }
        
        int ctx = -1;
        arraysort(*ships, *ns, cmp, &ctx);    
    }
    
    

    //****** generate ship configuration

    // H x W layers of positions blocked by the 1st, 2nd, ... ships
    bool **blocked[*ns-1], *blocked_[(*ns-1)*h], blocked__[(*ns-1)*h*w];
    for (k = 0; k < *ns-1; k++) {
        blocked[k] = blocked_ + k*h;
        for (i = 0; i < h; i++) {
            blocked_[k*h+i] = blocked__ + (k*h+i)*w;
        }
    }
    for (k = 0; k < (*ns-1)*h*w; k++) blocked__[k] = 0;

    // num_ships x 3 array of ship coordinates (vert, y, x);
    int *ship_coord[*ns], ship_coord_[*ns*3];
    for (k = 0; k < *ns; k++) ship_coord[k] = ship_coord_ + k*3;

    // count the total number of calls of the recursive function
    int gen_count[1];
    // limit on calls of the recursive function before another attempt 
    // to generate a solution is made
    int gen_count_lim = 1200;
    // maximum number of attempts to generate a solution before
    // number of ships is reduced 
    int attempt_lim = 5;

    while (true) {
        
        for (i = 0; i < attempt_lim; i++) {
            for (k = 0; k < (*ns-1)*h*w; k++) blocked__[k] = 0;
            for (k = 0; k < *ns*3; k++) ship_coord_[k] = 0;
            *gen_count = 0;
            
            err = place_ship_rng(
              0, params, *ships, ns, blocked, rs, ship_coord, 
              gen_count, gen_count_lim
            ); 
            
            if (! err) break;
        }
        if (! err) break;
    
        // ship configuration could not be generated: remove one ship
        ship_ex = ((int) (*ns + 1)/2) - 1; 
        memcpy(
          *ships + ship_ex, *ships + ship_ex + 1, 
          sizeof(int)*(*ns - ship_ex - 1)
        );
        (*ns)--;
    }
 


    //****** define parameters for puzzle generation
    
    // target solver count for difficulty 3 (min, max)
    int solver_count_int [2] = {50, 600};
    // values of array specify how many cells of the type -1/0/(1..6), 
    // respectively, are initially disclosed
    int ini_cells[3];
    // number of the sum values along the border that are hidden
    int sums_ex;
    // sum of all ship sizes
    int num_cells = 0;
    for (i = 0; i < *ns; i++) num_cells += (*ships)[i];
    
    int type_12, type_1;

    // specify parameters according to difficulty
    switch (diff) {
        case BASIC:
            sums_ex = 0;
            // no cells of type OCCUP disclosed; number of disclosed cells 
            // of type VACANT determined as a proportion of empty cells; 
            // number of disclosed cells of type (1..6) determined 
            // as a proportion of filled cells
            ini_cells[0] = round((h*w - num_cells)*0.2);
            ini_cells[1] = 0;
            ini_cells[2] = round(num_cells*0.6);
            break;
        case INTERMEDIATE:
            sums_ex = 0;
            ini_cells[0] = round((h*w - num_cells)*0.1);
            // count types 0 and (1..6) together with type 0 half-weighted
            type_12 = round(num_cells*0.3);
            type_1 = random_upto(rs, round(num_cells*0.2));
            ini_cells[1] = type_1*2;
            ini_cells[2] = type_12 - type_1;
            break;
        case ADVANCED:
            sums_ex = round((h + w)*.1) + random_upto(rs, 2);
            ini_cells[0] = round((h*w - num_cells)*0.05);
            type_12 = round(num_cells*0.2);
            type_1 = random_upto(rs, type_12); // 0, ..., type_12 - 1
            ini_cells[1] = type_1*2; 
            ini_cells[2] = type_12 - type_1;
            break;
        case UNREASONABLE:
            sums_ex = round((h + w)*.2) + random_upto(rs, 3);
            ini_cells[0] = 0; // no cells of type -1
            type_12 = round(num_cells*0.15);
            type_1 = random_upto(rs, type_12 + 1); // 0, ..., type_12
            ini_cells[1] = type_1;  // not multiplied by 2
            ini_cells[2] = type_12 - type_1;
    }
    ini_cells[0] = min(ini_cells[0], h*w - num_cells);
    if (ini_cells[1] + ini_cells[2] > num_cells) {
        ini_cells[1] = 0; ini_cells[2] = num_cells;
    }



    //****** 1st attempt to determine sum values along the border
    //****** and initially disclosed cells
    
    // H x W array of ship positions
    bool *ship_pos[h], ship_pos_[h*w];
    for (i = 0; i < h; i++) ship_pos[i] = ship_pos_ + i*w;
    for (i = 0; i < h*w; i++) ship_pos_[i] = 0;
    
    for (k = 0; k < *ns; k++) {
        for (i = 0; i < (*ships)[k]; i++) {
            ship_pos 
              [ship_coord[k][1]+i*ship_coord[k][0]] 
              [ship_coord[k][2]+i*(1-ship_coord[k][0])] 
              = 1
            ;
        }
    }
    
    // sum values along the border
    for (i = 0; i < h; i++) {
        rows[i] = 0;
        for (j = 0; j < w; j++) rows[i] += ship_pos[i][j];
    }
    for (j = 0; j < w; j++) {
        cols[j] = 0;
        for (i = 0; i < h; i++) cols[j] += ship_pos[i][j];
    }
    // make copies
    int rows0[h], cols0[w];
    memcpy(rows0, rows, sizeof(*rows)*h);
    memcpy(cols0, cols, sizeof(*cols)*w);
    // to hide sums_ex values, shuffle array {0, 1, ..., h+w-1}
    if (sums_ex > 0) {
        int ind[h+w];
        for (i = 0; i < h+w; i++) ind[i] = i;
        shuffle(ind, h+w, sizeof(*ind), rs);
        for (i = 0; i < sums_ex; i++) {
            if (ind[i] < h) rows[ind[i]] = -1;
            else            cols[ind[i]-h] = -1;
        }
    }    
    
    // initially disclosed cells
    
    // cumulated sum:
    int ships_aggr[*ns];
    ships_aggr[0] = (*ships)[0];
    for (k = 1; k < *ns; k++) ships_aggr[k] = ships_aggr[k-1] + (*ships)[k];
    
    // initialize array
    for (i = 0; i < h*w; i++) (*init)[i] = UNDEF;
    
    // choose ini_cells[1] + ini_cells[2] cells from num_cells
    int ind[num_cells], shift, ship;
    for (i = 0; i < num_cells; i++) ind[i] = i;
    shuffle(ind, num_cells, sizeof(*ind), rs);
    // cells of type OCCUP
    for (i = 0; i < ini_cells[1]; i++) {
        for (k = 0; k < *ns; k++) {
            if (ships_aggr[k] > ind[i]) break;
        }
        shift = ships_aggr[k] - ind[i] - 1; // shift along the ship
        init 
          [ship_coord[k][1] + shift*ship_coord[k][0]] 
          [ship_coord[k][2] + shift*(1-ship_coord[k][0])] 
          = OCCUP
        ;
    }
    // cells of type 1-6
    for (i = ini_cells[1]; i < ini_cells[1] + ini_cells[2]; i++) {
        for (k = 0; k < *ns; k++) {
            if (ships_aggr[k] > ind[i]) break;
        }
        shift = ships_aggr[k] - ind[i] - 1;
        ship = (*ships)[k];
        if (ship == 1) init[ship_coord[k][1]] [ship_coord[k][2]] = ONE;
        else if (shift == 0)
          init [ship_coord[k][1]] [ship_coord[k][2]] =
          NORTH*ship_coord[k][0] + WEST*(1 - ship_coord[k][0])
        ;
        else if (shift == ship - 1) 
          init 
            [ship_coord[k][1] + shift*ship_coord[k][0]] 
            [ship_coord[k][2] + shift*(1-ship_coord[k][0])] 
          = SOUTH*ship_coord[k][0] + EAST*(1 - ship_coord[k][0])
        ;
        else 
          init 
            [ship_coord[k][1] + shift*ship_coord[k][0]] 
            [ship_coord[k][2] + shift*(1-ship_coord[k][0])] 
          = INNER
        ;
    }
    // cells of type VACANT
    if (ini_cells[0] > 0) {
        int ind_[h*w - num_cells];
        for (i = 0; i < h*w-num_cells; i++) ind_[i] = i;
        shuffle(ind_, h*w-num_cells, sizeof(*ind_), rs);
        // sort the first ini_cells[0] elements
        int ctx = 1;
        arraysort(ind_, ini_cells[0], cmp, &ctx);
        int pos, pos0 = -1; 
        k = 0;
        for (pos = 0; pos < h*w; pos++) {
            i = (int) (pos/w);
            j = pos - i*w;
            if (ship_pos[i][j] == 0) pos0++;
            if (pos0 == ind_[k]) {
                init[i][j] = VACANT;
                k++;
                if (k == ini_cells[0]) break;
            }
        }
    }
    
    

    //****** check solution; adjust disclosed information, if needed
    
    struct sol soln;
    if (diff == 3) {
        soln.ship_coord  = snewn(*ns, int*);
        soln.ship_coord2 = snewn(*ns, int*);
        soln.ship_coord[0]  = snewn(*ns*3, int);
        soln.ship_coord2[0] = snewn(*ns*3, int);
        for (i = 1; i < *ns; i++) {
            soln.ship_coord[i]  = soln.ship_coord[0]  + i*3;
            soln.ship_coord2[i] = soln.ship_coord2[0] + i*3;
        }
    }
    
    struct game_state_const init_state;
    init_state.H         = h;
    init_state.W         = w;
    init_state.num_ships = *ns;
    init_state.ships     = *ships;
    init_state.init      = init;
    init_state.rows      = rows;
    init_state.cols      = cols;
    init_state.ships_sum = num_cells;
    
    // array where the resulting configuration from logical solver is written
    int *grid[h], grid_[h*w];
    for (i = 0; i < h; i++) {
        grid[i] = grid_ + i*w;
    }
    // variables where the number of occupied/vacant cells found 
    // by the logical solver is written
    int occ, vac;
        
    bool fast_return = false;
    int try_before_fast_return = 0;
    
    while (true) {

        init_state.rows_sum  = 0;
        for (i = 0; i < h; i++) {
            if (rows[i] > -1) init_state.rows_sum += rows[i];
        } 
        init_state.cols_sum = 0;
        for (j = 0; j < w; j++) {
            if (cols[j] > -1) init_state.cols_sum += cols[j];
        }
    
        // check if a unique solution exists 
        // logical solver
        log_solve = solve_by_logic(diff, &init_state, grid, &occ, &vac);
        // for unreasonable level solve with general solver
        if (diff == 3) solver(&init_state, solver_count_int[diff*2+1], &soln);
        
               
        // unique solution exists, difficulty ok or fast_return = true
        if (
          diff <= 1 && log_solve == 0  ||
          diff == 2 && (log_solve == 1 || log_solve == 0 && fast_return) ||
          diff == 3 && soln.err == 0 && 
            (
              soln.count >= solver_count_int[0] && log_solve == 2 ||
              fast_return
            )
        ) return;
            
            
        // unique solution exists, but too easy: increase difficulty
        else if (
          diff == 2 && log_solve == 0 ||
          diff == 3 && soln.err == 0 && (
            soln.count < solver_count_int[0] || log_solve < 2
          )
        ) {
        
            change = random_upto(rs, 2);
                
            // increase sums_ex by 1
            if (change == 0 && h + w - sums_ex > 0) {
                ex = random_upto(rs, h + w - sums_ex);
                k = 0;
                for (j = 0; j < h; j++) {
                     if (rows[j] != -1) {
                        if (k == ex) {rows[j] = -1; break;}
                        else k++;
                    }
                }
                if (k < ex) {
                    for (j = h; j < h+w; j++) {
                        if (rows[j-h] != -1) {
                            if (k == ex) {rows[j-h] = -1; break;}
                            else k++;
                        }
                    }
                }
                sums_ex++;
            }
                
            // change one element of init to -2
            else {
                num_init = ini_cells[0] + ini_cells[1] + ini_cells[2];
                if (num_init > 0) {
                    ex = random_upto(rs, num_init);
                    k = 0;
                    for (i = 0; i < h*w; i++) {
                        if ((*init)[i] != UNDEF) {
                            if (k == ex) {
                                if ((*init)[i] == VACANT) 
                                  (ini_cells[0])--
                                ;
                                else if ((*init)[i] == OCCUP)
                                  (ini_cells[1])--
                                ;
                                else (ini_cells[2])--;
                                (*init)[i] = UNDEF;
                                break;
                                }
                                else k++;
                        }
                    }
                }
            }
            
        }
        
        
        // more than one solution (diff == 3): set init = VACANT at one cell, 
        // which is actually vacant, but the solver yields "occupied"; 
        // return as soon as soln.count is below the upper limit 
        // (set fast_return = true)
        else if (diff == 3 && soln.err == 2) {
            fast_return = true;
            
            // number of "wrong" cells
            num_wrong = 0;
            for (k = 0; k < *ns; k++) {
                for (i = 0; i < (*ships)[k]; i++) {
                    if (
                      ship_pos 
                        [soln.ship_coord[k][1]+i*soln.ship_coord[k][0]] 
                        [soln.ship_coord[k][2]+i*(1-soln.ship_coord[k][0])] 
                      == 0
                      ||
                      ship_pos 
                        [soln.ship_coord2[k][1]+i*soln.ship_coord2[k][0]] 
                        [soln.ship_coord2[k][2]+i*(1-soln.ship_coord2[k][0])] 
                      == 0
                    ) num_wrong++;
                }
            }
            
            ex = random_upto(rs, num_wrong);
            j = 0;
            flag_break = false;
            for (k = 0; k < *ns; k++) {
                for (i = 0; i < (*ships)[k]; i++) {
                    if (
                      ship_pos 
                        [soln.ship_coord[k][1]+i*soln.ship_coord[k][0]] 
                        [soln.ship_coord[k][2]+i*(1-soln.ship_coord[k][0])] 
                      == 0
                      ||
                      ship_pos 
                        [soln.ship_coord2[k][1]+i*soln.ship_coord2[k][0]] 
                        [soln.ship_coord2[k][2]+i*(1-soln.ship_coord2[k][0])] 
                      == 0
                    ) {
                        if (j == ex) {
                            (ini_cells[0])++;
                            if (
                              ship_pos 
                                [
                                  soln.ship_coord[k][1]
                                  +i*soln.ship_coord[k][0]
                                ] 
                                [
                                  soln.ship_coord[k][2]
                                  +i*(1-soln.ship_coord[k][0])
                                ] 
                              == 0
                            )
                              init 
                                [
                                  soln.ship_coord[k][1]
                                  +i*soln.ship_coord[k][0]
                                ] 
                                [
                                  soln.ship_coord[k][2]
                                  +i*(1-soln.ship_coord[k][0])
                                ] 
                              = VACANT
                            ;
                            else
                              init 
                                [
                                  soln.ship_coord2[k][1]
                                  +i*soln.ship_coord2[k][0]
                                ] 
                                [
                                  soln.ship_coord2[k][2]
                                  +i*(1-soln.ship_coord2[k][0])
                                ] 
                              = VACANT
                            ;
                            flag_break = true;
                            break;
                        }
                        else j++;
                    }
                }
                if (flag_break) break;
            }            
        }
        
        
        // no solution found or too difficult:
        // decrease difficulty, return as soon as not too difficult 
        // (set fast_return = true) 
        else {
            try_before_fast_return++;
            if (try_before_fast_return > 0) fast_return = true;
            
            change = random_upto(rs, 5);
            
            // decrease sums_ex by 1
            if (change == 0 && sums_ex > 0) {
                ex = random_upto(rs, sums_ex);
                k = 0;
                for (j = 0; j < h; j++) {
                    if (rows[j] == -1) {
                        if (k == ex) {rows[j] = rows0[j]; break;}
                        k++;
                    }
                }
                if (k < ex) {
                    for (j = h; j < h+w; j++) {
                        if (cols[j-h] == -1) {
                            if (k == ex) {cols[j-h] = cols0[j-h]; break;}
                            k++;
                        }
                    }
                }
                sums_ex--;
            }
            
            // change one element of init from UNDEF to VACANT;
            // in case of logical solution change elements not found by solver
            else if (change < 4) {
                if (diff <= 2) num_init = h*w - num_cells - vac;
                else           num_init = h*w - num_cells - ini_cells[0];
                k = 0;
                if (num_init > 0) {
                    ex = random_upto(rs, num_init);
                    flag_break = false;
                    for (i = 0; i < h; i++) {
                        for (j = 0; j < w; j++) {
                            if (
                              (  diff <= 2 && grid[i][j] == UNDEF || 
                                 diff == 3 && init[i][j] == UNDEF   ) &&
                              ! ship_pos[i][j]
                            ) {
                                if (k == ex) {
                                    init[i][j] = VACANT; 
                                    flag_break = true;
                                    (ini_cells[0])++;
                                    break;
                                }
                                k++;
                            }
                        }
                        if (flag_break) break;
                    }
                }
            }
            
            // change one element of init from UNDEF to 1 .. 6
            else {
                if (diff <= 2) num_init = num_cells - occ;
                else      num_init = num_cells - ini_cells[1] - ini_cells[2];
                if (num_init > 0) {
                    ex = random_upto(rs, num_init);
                    j = 0;
                    flag_break = false;
                    for (k = 0; k < *ns; k++) {
                        for (i = 0; i < (*ships)[k]; i++) {
                            if (
                              diff <= 2 &&
                              grid 
                                [ship_coord[k][1]+i*ship_coord[k][0]] 
                                [ship_coord[k][2]+i*(1-ship_coord[k][0])] 
                              == UNDEF ||
                              diff == 3 &&
                              init 
                                [ship_coord[k][1]+i*ship_coord[k][0]] 
                                [ship_coord[k][2]+i*(1-ship_coord[k][0])] 
                              == UNDEF
                            ) {
                                if (j == ex) {
                                    if ((*ships)[k] == 1)
                                      init 
                                        [ship_coord[k][1]] 
                                        [ship_coord[k][2]] 
                                      = ONE
                                    ;
                                    else if (0 < i && i < (*ships)[k] - 1)
                                      init 
                                        [ship_coord[k][1]+i*ship_coord[k][0]] 
                                        [
                                          ship_coord[k][2]+
                                          i*(1-ship_coord[k][0])
                                        ] 
                                      = INNER
                                    ;
                                    else if (i == 0 && ship_coord[k][0])
                                      init 
                                        [ship_coord[k][1]+i*ship_coord[k][0]] 
                                        [
                                          ship_coord[k][2]+
                                          i*(1-ship_coord[k][0])
                                        ] 
                                      = NORTH
                                    ;
                                    else if (i == 0 && ! ship_coord[k][0])
                                      init 
                                        [ship_coord[k][1]+i*ship_coord[k][0]] 
                                        [
                                          ship_coord[k][2]+
                                          i*(1-ship_coord[k][0])
                                        ] 
                                      = WEST
                                    ;
                                    else if (
                                      i == (*ships)[k]-1 && ship_coord[k][0]
                                    )
                                      init 
                                        [ship_coord[k][1]+i*ship_coord[k][0]] 
                                        [
                                          ship_coord[k][2]+
                                          i*(1-ship_coord[k][0])
                                        ] 
                                      = SOUTH
                                    ;
                                    else if (
                                      i == (*ships)[k]-1 && ! ship_coord[k][0]
                                    )
                                      init 
                                        [ship_coord[k][1]+i*ship_coord[k][0]] 
                                        [
                                          ship_coord[k][2]+
                                          i*(1-ship_coord[k][0])
                                        ] 
                                      = EAST
                                    ;
                                    flag_break = true;
                                    break;
                                }
                                else j++;
                            }
                        }
                        if (flag_break) break;
                    }
                    (ini_cells[2])++;
                }
                // escape in the improbable case that all ship cells 
                // are specified 1 .. 6
                else return;
            }
        }
        
    }
    
    if (diff == 3) {
        sfree(soln.ship_coord[0]);
        sfree(soln.ship_coord2[0]);
        sfree(soln.ship_coord);
        sfree(soln.ship_coord2);
    }
}


/* 
Recursive procedure for the function generator_diff() to generate a random
configuration of the ships.

Parameters:
  ship_num: current ship number 0, ..., ns-1 (ns = number of ships);
  *params: game parameters;
  *ships: array of ship sizes;
  *num_ships: number of ships;
  ***blocked: 3D array which consists of H x W layers of positions blocked by
the 1st, 2nd, ... ships (H = height, W= width);
  *rs: random state;
  **ship_coord: ns x 3 temporary array of ship coordinates (vert, y, x) 
per ship;
  *count: number of times the recursive function place_ship_rng() is called;
  count_lim: maximum number of times the recursive function place_ship_rng()
can be called, before the attempt is interrupted and an error returned; set 
to a value of 0 or less if no limit is desired.

The function returns an error value true/false.
  
*/
static bool place_ship_rng(
  int ship_num, const game_params *params, int *ships, int *num_ships, 
  bool ***blocked, random_state *rs, int **ship_coord, int *count, 
  int count_lim
) 
{
    (*count)++;
    if (0 < count_lim && count_lim < *count) return true;

    int h = params->H, w = params->W, ns = *num_ships;
    int ship = ships[ship_num];
    int num_pos, pos, vert, y, x, i, j, k, ship_H, ship_W;
    bool err, brk;
    
    // number of positions for horizontal and vertical orientation
    // (double count for ship length 1 does not lead to an error)
    num_pos = h*(w - ship + 1) + (h - ship + 1)*w;
    
    while (true) {
    
        // generate position
        pos = random_upto(rs, num_pos);
        
        // horizontal
        if (pos < h*(w - ship + 1)) {
            vert = 0;
            y = (int) (pos/(w - ship + 1));
            x = pos - y*(w - ship + 1);
        }
        // vertical
        else {
            pos = pos - h*(w - ship + 1);
            vert = 1;
            y = (int) (pos/w);
            x = pos - y*w;
        }
    
        // ship dimensions
        ship_H = vert*ship + 1 - vert;
        ship_W = (1 - vert)*ship + vert;
        
        // check that cells not blocked 
        brk = false;
        for (k = 0; k < ship_num; k++) {
            for (i = 0; i < ship_H; i++) {
                for (j = 0; j < ship_W; j++) {
                    if (blocked[k][y+i][x+j]) {brk = true; break;}
                }
                if (brk) break;
            }
            if (brk) break;
        }
        if (brk) return true;
        
        // not last ship
        if (ship_num < ns - 1) {
                        
            // block cells of and around the ship
            for (i = max(y-1, 0); i < min(y + ship_H + 1, h); i++) {
                for (j = max(x-1, 0); j < min(x + ship_W + 1, w); j++) {
                    blocked[ship_num][i][j] = 1;
                }
            }
           
            //recursive call
            err = place_ship_rng(
              ship_num + 1, params, ships, num_ships, blocked, rs, ship_coord, 
              count, count_lim
            );

            // if next ship could not be placed, replace current ship
            // and unblock or return error if count_lim exceeded
            if (err) {
                if (count_lim <= 0 || *count <= count_lim) {
                    for (i = 0; i < h*w; i++)  (*(blocked[ship_num]))[i] = 0;
                }
                else return true;
            }
            // record current position and return
            else {
                ship_coord[ship_num][0] = vert;
                ship_coord[ship_num][1] = y;
                ship_coord[ship_num][2] = x;
                return false;
            }
        }
        
        // last ship 
        else {
            ship_coord[ship_num][0] = vert;
            ship_coord[ship_num][1] = y;
            ship_coord[ship_num][2] = x;
            return false;
        }
        
    }
    
}

/* 
Draw ship segments, see enum Configuration 
  
Parameters:
  *dr: drawing object;
  conf: element id as in enum Configuration (-1 .. 6);
  tilesize;
  xf, yf: left upper corner of the square tile frame 
(square edge is tilesize + 1);
  color: color of the element (for conf == 0 not relevant, set to -1, e.g.);
  color_bg: color of the cell background (set to -1 if not needed, e.g., 
for printing).
*/
static void draw_segment(
  drawing *dr, const enum Configuration conf, const int tilesize, 
  const int xf, const int yf, const int color, const int color_bg
)
{
    int elem_size, shift, coords3[6], coords4[8];
    int const ts = tilesize;
    
    switch (conf) {
        case VACANT:
            if (color_bg >= 0) 
              draw_rect(dr, xf + 1, yf + 1, ts - 1, ts - 1, color_bg)
            ;
            elem_size = ts/10 + 1;
            shift = max((ts - elem_size - 1)/2, 3);
            elem_size = ts - 1 - 2*shift;   // adjust when ts-elem_size-1 odd
            draw_rect(
              dr, xf + shift + 1, yf + shift + 1, elem_size, elem_size, color
            );
            break;
        case OCCUP:
            if (color_bg >= 0) 
              draw_rect(dr, xf + 1, yf + 1, ts - 1, ts - 1, color_bg)
            ;
            break;
        case NORTH:
            if (color_bg >= 0) 
              draw_rect(dr, xf + 1, yf + 1, ts - 1, ts - 1, color_bg)
            ;
            elem_size = ts*6/10 + 1;
            shift = max((ts - elem_size - 1)/2, 3);
            elem_size = ts - 1 - 2*shift;
            coords3[0] = xf + (ts - 1)/2 + 1; 
            coords3[1] = yf + shift + 1;
            coords3[2] = xf + shift + 1; 
            coords3[3] = yf + shift + elem_size;
            coords3[4] = xf + shift + elem_size; 
            coords3[5] = yf + shift + elem_size;
            draw_polygon(dr, coords3, 3, color, color);
            break;
        case EAST:
            if (color_bg >= 0) 
              draw_rect(dr, xf + 1, yf + 1, ts - 1, ts - 1, color_bg)
            ;
            elem_size = ts*6/10 + 1;
            shift = max((ts - elem_size - 1)/2, 3);
            elem_size = ts - 1 - 2*shift;
            coords3[0] = xf + shift + 1; 
            coords3[1] = yf + shift + 1;
            coords3[2] = xf + shift + elem_size; 
            coords3[3] = yf + (ts - 1)/2 + 1;
            coords3[4] = xf + shift + 1; 
            coords3[5] = yf + shift + elem_size;
            draw_polygon(dr, coords3, 3, color, color);
            break;
        case SOUTH:
            if (color_bg >= 0) 
              draw_rect(dr, xf + 1, yf + 1, ts - 1, ts - 1, color_bg)
            ;
            elem_size = ts*6/10 + 1;
            shift = max((ts - elem_size - 1)/2, 3);
            elem_size = ts - 1 - 2*shift;
            coords3[0] = xf + shift + 1; 
            coords3[1] = yf + shift + 1;
            coords3[2] = xf + shift + elem_size; 
            coords3[3] = yf + shift + 1;
            coords3[4] = xf + (ts - 1)/2 + 1; 
            coords3[5] = yf + shift + elem_size;
            draw_polygon(dr, coords3, 3, color, color);
            break;
        case WEST:
            if (color_bg >= 0) 
              draw_rect(dr, xf + 1, yf + 1, ts - 1, ts - 1, color_bg)
            ;
            elem_size = ts*6/10 + 1;
            shift = max((ts - elem_size - 1)/2, 3);
            elem_size = ts - 1 - 2*shift;
            coords3[0] = xf + shift + 1; 
            coords3[1] = yf + (ts - 1)/2 + 1;
            coords3[2] = xf + shift + elem_size; 
            coords3[3] = yf + shift + 1;
            coords3[4] = xf + shift + elem_size; 
            coords3[5] = yf + shift + elem_size;
            draw_polygon(dr, coords3, 3, color, color);
            break;
        case ONE:
            if (color_bg >= 0) 
              draw_rect(dr, xf + 1, yf + 1, ts - 1, ts - 1, color_bg)
            ;
            elem_size = ts*6/10 + 1;
            shift = max((ts - elem_size - 1)/2, 3);
            elem_size = ts - 1 - 2*shift;
            coords4[0] = xf + (ts - 1)/2 + 1; 
            coords4[1] = yf + shift + 1;
            coords4[2] = xf + shift + elem_size; 
            coords4[3] = yf + (ts - 1)/2 + 1;
            coords4[4] = xf + (ts - 1)/2 + 1; 
            coords4[5] = yf + shift + elem_size;
            coords4[6] = xf + shift + 1; 
            coords4[7] = yf + (ts - 1)/2 + 1;
            draw_polygon(dr, coords4, 4, color, color);
            break;
        case INNER:
            if (color_bg >= 0) 
              draw_rect(dr, xf + 1, yf + 1, ts - 1, ts - 1, color_bg)
            ;
            elem_size = ts*6/10 + 1;
            shift = max((ts - elem_size - 1)/2, 3);
            elem_size = ts - 1 - 2*shift;
            draw_rect(
              dr, xf + shift + 1, yf + shift + 1, elem_size, elem_size, color
            );
    }
}



/* 
Draw cells 
  
Parameters:
  *dr: drawing object;
  *state: game_state;
  xc, yc: coordinates of the cell counted from the left upper corner;
  tilesize;
  x0pt, y0pt: point coordinates of the upper left corner of the frame of the cell with xc = yc = 0; the point coordinates are counted from the upper left corner of the drawing field;
  cursor: true if cursor is to be shown in the cell;
  error: true if error is to be shown in the cell;
  update: true if draw_update() function is to be executed for the cell;
  drag: true if drag is underway;
  clear: true if drag clears cells (disregarded if drag == false);
  conf: type of segment (-1..6) to draw during drag  (disregarded if 
drag == false or clear == true);
  flash: true if flash is underway.
*/
static void draw_cell(
  drawing *dr, const game_state *state, int xc, int yc, 
  int tilesize, int x0pt, int y0pt, bool cursor, bool error, bool update,
  bool drag, bool clear, enum Configuration conf, bool flash
)
{
    int const ts = tilesize;
    int i, j, color_bg, coords3[6];
    int cell_state = ((drag && ! clear) ? conf : state->grid_state [yc][xc]);
    
    // empty
    if (cell_state == UNDEF) {
        if (flash) color_bg = COL_FLASH; else color_bg = COL_BACKGROUND;
        draw_rect(
          dr, x0pt + ts*xc + 1, y0pt + ts*yc + 1, ts - 1, ts - 1, color_bg
        );
    }
    // filled
    else {
        if (flash) color_bg = COL_FLASH; 
        else if (cell_state == VACANT) color_bg = COL_BACKGROUND;
        else color_bg = COL_OCCUP;
        draw_segment(
          dr, cell_state, ts, x0pt + ts*xc, y0pt + ts*yc, 
          (! error ? (! drag ? COL_SEGMENT : COL_DRAG) : COL_ERROR), 
          (error && cell_state == OCCUP ? COL_ERROR : color_bg)
        );
    }
    // cursor
    if (cursor) {
        coords3[0] = x0pt + ts*xc + 1; 
        coords3[1] = y0pt + ts*yc + 1;
        coords3[2] = x0pt + ts*xc + 5*ts/10; 
        coords3[3] = y0pt + ts*yc + 1;
        coords3[4] = x0pt + ts*xc + 1; 
        coords3[5] = y0pt + ts*yc + 5*ts/10;
        draw_polygon(dr, coords3, 3, COL_HIGHLIGHT, COL_HIGHLIGHT);
    }
    // initially disclosed: thick border
    if ((state->init_state->init)[yc][xc] > -2) {
        draw_rect_outline(
          dr, x0pt + ts*xc + 1, y0pt + ts*yc + 1, ts - 1, ts - 1, COL_GRID
        );
        if (ts > 22) {
            draw_rect_outline(
              dr, x0pt + ts*xc + 2, y0pt + ts*yc + 2, ts - 3, ts - 3, COL_GRID
            );
        }
    }
    
    if (update) {
        draw_update(dr, x0pt + ts*xc + 1, y0pt + ts*yc + 1, ts - 1, ts - 1);
    }
}



/*
Validate for errors and check if solved

Parameters:
  *state: game_state;
  *solved: the variable is true if the puzzle is solved.
  
The function calculates the following elements of struct state:
  **grid_state_err,
  *rows_err, 
  *cols_err,
  ships_err,
  *ships_state.

*/
static void validation(game_state *state, bool *solved)
{
    int h = state->init_state->H, w = state->init_state->W;
    int ns = state->init_state->num_ships;
    bool **grid_state_err = state->grid_state_err;
    int **grid_state = state->grid_state;
    int i, j, k, l, sum, sum1; 
    int max_ship = state->init_state->ships [0], distr[max_ship];  
    
    // initial values
    for (i = 0; i < h; i++) {
        for (j = 0; j < w; j++) {
            grid_state_err[i][j] = false;
        }
        state->rows_err[i] = false;
    }
    for (j = 0; j < w; j++) state->cols_err[j] = false;
    state->ships_err = false;
    for (i = 0; i < max_ship; i++) distr[i] = 0;
    for (i = 0; i < ns; i++) state->ships_state[i] = false;
    *solved = true;
    
    // neighbor consistency
    for (i = 0; i < h; i++) {
        for (j = 0; j < w; j++) {
        
            // no diagonal neighbors
            for (k = -1; k <= 1; k += 2) {
                for (l = -1; l <= 1; l += 2) {
                   if (
                      0 <= i+k && i+k < h && 0 <= j+l && j+l < w && 
                      grid_state[i][j] >= 0 && grid_state[i+k][j+l] >= 0
                    ) {
                        grid_state_err[i][j] = true;
                       *solved = false;
                    }
                }
            }
            
            // check neighbors of VACANT 
            #define CASE_VACANT(i, j, h, w, conf, mat, m, m_err)            \
                if (mat((i), (j), m, h, w) == VACANT && (                   \
                  0 <= (i)-1 && (                                           \
                    mat((i)-1, (j), m, h, w) == conf ||                     \
                    mat((i)-1, (j), m, h, w) == INNER &&                    \
                    (                                                       \
                      0 <= (i)-2 && mat((i)-2, (j), m, h, w) >= 0        || \
                      0 <= (j)-1 && mat((i)-1, (j)-1, m, h, w) == VACANT || \
                      (j)+1 < w  && mat((i)-1, (j)+1, m, h, w) == VACANT    \
                    )                                                       \
                  )                                                         \
                  ||                                                        \
                  (i) == 0 && (                                             \
                    0 <= (j)-1 && mat((i), (j)-1, m, h, w) == INNER         \
                    ||                                                      \
                    (j)+1 < w  && mat((i), (j)+1, m, h, w) == INNER         \
                  )                                                         \
                )) {                                                        \
                    mat((i), (j), m_err, h, w) = true;                      \
                    *solved = false;                                        \
                }
            // apply the above with rotation symmetry transformations
            CASE_VACANT(
              i,     j,     h, w, NORTH, MAT_0, grid_state, grid_state_err
            );  
            CASE_VACANT(
              w-1-j, i,     w, h, EAST,  MAT_1, grid_state, grid_state_err
            );  
            CASE_VACANT(
              h-1-i, w-1-j, h, w, SOUTH, MAT_2, grid_state, grid_state_err
            );   
            CASE_VACANT(
              j,     h-1-i, w, h, WEST,  MAT_3, grid_state, grid_state_err
            );  


            // check neighbors of OCCUP 
            #define CASE_OCCUP(i, j, h, w, conf, mat, m, m_err)  \
                if (mat((i), (j), m, h, w) == OCCUP && (         \
                  0 <= (i)-1 && ! (                              \
                      mat((i)-1, (j), m, h, w) == conf   ||      \
                      mat((i)-1, (j), m, h, w) == UNDEF  ||      \
                      mat((i)-1, (j), m, h, w) == VACANT ||      \
                      mat((i)-1, (j), m, h, w) == OCCUP  ||      \
                      mat((i)-1, (j), m, h, w) == INNER          \
                  )                                              \
                )) {                                             \
                    mat((i), (j), m_err, h, w) = true;           \
                    *solved = false;                             \
                }
            CASE_OCCUP(
              i,     j,     h, w, NORTH, MAT_0, grid_state, grid_state_err
            );  
            CASE_OCCUP(
              w-1-j, i,     w, h, EAST,  MAT_1, grid_state, grid_state_err
            );  
            CASE_OCCUP(
              h-1-i, w-1-j, h, w, SOUTH, MAT_2, grid_state, grid_state_err
            );   
            CASE_OCCUP(
              j,     h-1-i, w, h, WEST,  MAT_3, grid_state, grid_state_err
            );  


            // check neighbors of NORTH, SOUTH, EAST, WEST
            #define CASE_NSEW(i, j, h, w, conf, mat, m, m_err)        \
                if (mat((i), (j), m, h, w) == conf && (               \
                  0 <= (i)-1 && mat((i)-1, (j), m, h, w) >= 0         \
                  ||                                                  \
                  (i)+1 < h && ! (                                    \
                    mat((i)+1, (j), m, h, w) == (conf + 1) % 4 + 1 || \
                    mat((i)+1, (j), m, h, w) == UNDEF ||              \
                    mat((i)+1, (j), m, h, w) == OCCUP ||              \
                    mat((i)+1, (j), m, h, w) == INNER                 \
                  )                                                   \
                  ||                                                  \
                  0 <= (j)-1 && mat((i), (j)-1, m, h, w) >= 0         \
                  ||                                                  \
                  (j)+1 < w  && mat((i), (j)+1, m, h, w) >= 0         \
                  ||                                                  \
                  (i) == h-1                                          \
                )) {                                                  \
                    mat((i), (j), m_err, h, w) = true;                \
                    *solved = false;                                  \
                }
            CASE_NSEW(
              i,     j,     h, w, NORTH, MAT_0, grid_state, grid_state_err
            );  
            CASE_NSEW(
              w-1-j, i,     w, h, EAST,  MAT_1, grid_state, grid_state_err
            );  
            CASE_NSEW(
              h-1-i, w-1-j, h, w, SOUTH, MAT_2, grid_state, grid_state_err
            );   
            CASE_NSEW(
              j,     h-1-i, w, h, WEST,  MAT_3, grid_state, grid_state_err
            );  
                
                
            // check neighbors of ONE
            if (grid_state[i][j] == ONE && ( 
                0 <= i-1 && grid_state[i-1][j] >= 0 
                ||
                i+1 < h && grid_state[i+1][j] >= 0 
                ||
                0 <= j-1 && grid_state[i][j-1] >= 0 
                ||
                j+1 < w && grid_state[i][j+1] >= 0 
            )) {
                grid_state_err[i][j] = true;
                *solved = false;
            }
                    
                
            // check neighbors of INNER 
            #define CASE_INNER(i, j, h, w, conf, mat, m, m_err)      \
                if (mat((i), (j), m, h, w) == INNER && (             \
                  0 <= (i)-1 && ! (                                  \
                    mat((i)-1, (j), m, h, w) == conf  ||             \
                    mat((i)-1, (j), m, h, w) == UNDEF  ||            \
                    mat((i)-1, (j), m, h, w) == VACANT ||            \
                    mat((i)-1, (j), m, h, w) == OCCUP  ||            \
                    mat((i)-1, (j), m, h, w) == INNER                \
                  )                                                  \
                  ||                                                 \
                  (i) == 0 && (                                      \
                    mat((i)+1, (j), m, h, w) >= 0                    \
                    ||                                               \
                    0 <= (j)-1 && mat((i), (j)-1, m, h, w) == VACANT \
                    ||                                               \
                    (j)+1 < w  && mat((i), (j)+1, m, h, w) == VACANT \
                    ||                                               \
                    (j) == 0 || (j) == w-1                           \
                  )                                                  \
                  ||                                                 \
                  0 <= (i)-1 && 0 <= (j)-1 &&                        \
                  mat((i)-1, (j), m, h, w) == VACANT &&              \
                  mat((i), (j)-1, m, h, w) == VACANT                 \
                  ||                                                 \
                  0 <= (i)-1 && (i)+1 < h && (                       \
                    mat((i)-1, (j), m, h, w) == VACANT &&            \
                    mat((i)+1, (j), m, h, w) >= 0         ||         \
                    mat((i)-1, (j), m, h, w) >= 0      &&            \
                    mat((i)+1, (j), m, h, w) == VACANT               \
                  )                                                  \
                )) {                                                 \
                    mat((i), (j), m_err, h, w) = true;               \
                    *solved = false;                                 \
                }
            CASE_INNER(
              i,     j,     h, w, NORTH, MAT_0, grid_state, grid_state_err
            );  
            CASE_INNER(
              w-1-j, i,     w, h, EAST,  MAT_1, grid_state, grid_state_err
            );  
            CASE_INNER(
              h-1-i, w-1-j, h, w, SOUTH, MAT_2, grid_state, grid_state_err
            );   
            CASE_INNER(
              j,     h-1-i, w, h, WEST,  MAT_3, grid_state, grid_state_err
            );  

        }
    }
    
    
    // sums consistency
    // rows
    for (i = 0; i < h; i++) {
        sum  = 0;
        sum1 = 0;
        if (state->init_state->rows [i] >= 0) {
            for (j = 0; j < w; j++) {
                sum  += (grid_state[i][j] >= 0      ? 1 : 0);
                sum1 += (grid_state[i][j] == VACANT ? 1 : 0);
            }
            if (sum >  state->init_state->rows [i]) state->rows_err[i] = true;
            if (sum1 > w - state->init_state->rows [i]) 
              state->rows_err[i] = true
            ;
            if (sum != state->init_state->rows [i]) *solved = false;
        }
    }    
    // columns
    for (j = 0; j < w; j++) {
        sum = 0;
        sum1 = 0;
        if (state->init_state->cols [j] >= 0) {
            for (i = 0; i < h; i++) {
                sum  += (grid_state[i][j] >= 0      ? 1 : 0);
                sum1 += (grid_state[i][j] == VACANT ? 1 : 0);
            }
            if (sum >  state->init_state->cols [j]) state->cols_err[j] = true;
            if (sum1 > h - state->init_state->cols [j]) 
              state->cols_err[j] = true
            ;
            if (sum != state->init_state->cols [j]) *solved = false;
        }
    }    
    
    
    // ships consistency (only the ships are found that are searched for)
    state->ships_err = compl_ships_distr(h, w, grid_state, max_ship, distr);
    if (! state->ships_err) {
        for (k = 0; k < max_ship; k++) {
            if (distr[k] > state->init_state->ships_distr[k]) {
                state->ships_err = true;
                break;
            }
        }
    }
    if (state->ships_err) *solved = false;

   
    // mark ships done
    if (! state->ships_err) {
        for (i = 0; i < ns; i++) {
            if (distr [state->init_state->ships [i] - 1] > 0) {
                state->ships_state[i] = true;
                (distr [state->init_state->ships [i] - 1])--;
            }
            else *solved = false;
        }
    }

    
    // check (number of occupied and specified cells) = sum(ship sizes)
    if (*solved) {
        sum = 0;
        for (i = 0; i < h; i++) {
            for (j = 0; j < w; j++) {
                sum += (grid_state[i][j] > 0 ? 1 : 0);
            }
        }
        sum1 = 0;
        for (i = 0; i < ns; i++) sum1 += state->init_state->ships [i];
        if (sum != sum1) *solved = false;
    }
    
}


