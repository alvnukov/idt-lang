/* Independent full enumeration for the local-cell inference probe.
 * No Python decision tree and no wildcard tables. Each of 8^8 table IDs
 * is expanded and simulated. All outcomes concern an ideal prepared ring
 * and a prescribed first marked-return time; they are not physical verdicts.
 * Example: cc -std=c11 -O2 -Wall -Wextra -Werror scripts/audit_cell_census.c -o audit_cell
 */
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

enum { CASES = 22 };
struct event { unsigned when, memory; int direction; };

static struct event run(const unsigned char f[8], unsigned n, int d) {
    /* Directed position is the most recent vertex, counting the hub as 0.
     * Modular movement differs from the Python cut-open [0,n] segment. */
    unsigned pos = 0, tag = 1, cells = 0;
    for (unsigned tick = 1; tick <= n*n; ++tick) {
        pos = d > 0 ? (pos+1 == n ? 0 : pos+1) : (pos ? pos-1 : n-1);
        if (!pos) {
            if (tag) return (struct event){tick,cells,d};
        } else {
            const unsigned mask = 1U << (pos-1);
            unsigned out = f[(d < 0 ? 4U : 0U) | (tag << 1) | ((cells & mask) != 0)];
            cells = (cells & ~mask) | (out & 1U ? mask : 0U);
            tag = (out >> 1) & 1U;
            d = out < 4 ? -1 : 1;
        }
    }
    return (struct event){0,cells,d};
}

static void counts(const char *name, const uint32_t count[CASES+1]) {
    printf("%s",name);
    for (unsigned i=0; i<=CASES; ++i) printf(" %" PRIu32,count[i]);
    putchar('\n');
}

int main(int argc, char **argv) {
    const int list_ids = argc == 2 && strcmp(argv[1],"--survivors") == 0;
    if (argc != 1 && !list_ids) return 2;
    unsigned len[CASES] = {2,3,2,3};
    int dir[CASES] = {1,1,-1,-1};
    for (unsigned n=4; n<=12; ++n) {
        unsigned at = 4+2*(n-4);
        len[at] = len[at+1] = n; dir[at] = -1; dir[at+1] = 1;
    }
    uint32_t t[CASES+1] = {0}, f[CASES+1] = {0};
    for (uint32_t id=0; id < (UINT32_C(1)<<24); ++id) {
        unsigned char rule[8];
        for (unsigned j=0; j<8; ++j) rule[j] = (id >> (3*j)) & 7U;
        unsigned time_stop = CASES, full_stop = CASES;
        for (unsigned j=0; j<CASES; ++j) {
            struct event e = run(rule,len[j],dir[j]);
            int matched = e.when == len[j]*len[j];
            if (full_stop == CASES && (!matched || e.memory != 0 || e.direction != dir[j]))
                full_stop = j;
            if (!matched) {time_stop = j; break;}
        }
        ++t[time_stop]; ++f[full_stop];
        if (list_ids && time_stop == CASES)
            printf("id %" PRIu32 " %d\n",id,full_stop == CASES);
    }
    counts("time",t); counts("full",f);
    return 0;
}
