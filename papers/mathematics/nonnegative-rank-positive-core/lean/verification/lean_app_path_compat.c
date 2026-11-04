/* Compatibility fix for an executable-path lookup in a PID namespace.
 * This maps /proc/<our-namespace-pid>/exe to /proc/self/exe. The former
 * path is incorrect when /proc belongs to a containing PID namespace.
 * It does not replace any Lean parser, elaborator, evaluator, or kernel API.
 * The unmodified Lean distribution and its kernel remain in use.
 * Normal installations do not need this file.
 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

ssize_t readlink(const char *path, char *buf, size_t size) {
    typedef ssize_t (*readlink_fn)(const char *, char *, size_t);
    readlink_fn actual = (readlink_fn)dlsym(RTLD_NEXT, "readlink");
    if (actual == NULL) abort();
    char own_path[80];
    snprintf(own_path, sizeof(own_path), "/proc/%ld/exe", (long)getpid());
    return actual(strcmp(path, own_path) == 0 ? "/proc/self/exe" : path,
                  buf, size);
}
