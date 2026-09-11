/* Independent native allocation ledger; test-only GNU ld --wrap hooks. */
#include <stdlib.h>

void *__real_aligned_alloc(size_t alignment, size_t size);
void __real_free(void *pointer);

static void *live[64];
static size_t allocations, releases;
#ifdef EXPECTED_RELEASE_ORDER
static size_t identities[64], release_order;
#endif

void *__wrap_aligned_alloc(size_t alignment, size_t size) {
    void *pointer = __real_aligned_alloc(alignment, size);
    if (!pointer) return pointer;
    for (size_t i = 0; i < 64; ++i) {
        if (!live[i]) {
            live[i] = pointer;
            ++allocations;
#ifdef EXPECTED_RELEASE_ORDER
            identities[i] = allocations;
#endif
            return pointer;
        }
    }
    _Exit(120);
}

void __wrap_free(void *pointer) {
    if (!pointer) return; /* Moved native owner leaves use a null sentinel. */
    for (size_t i = 0; i < 64; ++i) {
        if (live[i] == pointer) {
            live[i] = NULL;
            ++releases;
#ifdef EXPECTED_RELEASE_ORDER
            release_order = release_order * 10 + identities[i];
#endif
            __real_free(pointer);
            return;
        }
    }
    _Exit(121); /* Double free or a pointer without allocation authority. */
}

__attribute__((destructor)) static void check_resources(void) {
    if (allocations != EXPECTED_ALLOCATIONS || releases != allocations) _Exit(122);
    for (size_t i = 0; i < 64; ++i) if (live[i]) _Exit(123);
#ifdef EXPECTED_RELEASE_ORDER
    if (release_order != EXPECTED_RELEASE_ORDER) _Exit(124);
#endif
}
