#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

typedef ssize_t (*readlink_fn)(const char *, char *, size_t);

/*
 * Some managed containers do not expose Lean's executable through procfs in
 * the form expected by the official distribution.  The local build wrapper
 * supplies the exact Lean executable through LEAN_PROC_SELF_EXE and this shim
 * answers only the two procfs reads used for executable discovery.
 */
ssize_t readlink(const char *path, char *buffer, size_t size) {
  const char *override = getenv("LEAN_PROC_SELF_EXE");
  char process_path[64];
  snprintf(process_path, sizeof(process_path), "/proc/%ld/exe", (long)getpid());

  if (override != NULL &&
      (strcmp(path, "/proc/self/exe") == 0 || strcmp(path, process_path) == 0)) {
    size_t length = strlen(override);
    size_t copied = length < size ? length : size;
    memcpy(buffer, override, copied);
    return (ssize_t)copied;
  }

  static readlink_fn original = NULL;
  if (original == NULL)
    original = (readlink_fn)dlsym(RTLD_NEXT, "readlink");
  return original(path, buffer, size);
}
