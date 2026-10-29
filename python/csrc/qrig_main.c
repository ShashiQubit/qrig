/*
 * qrig_main.c -- stand-alone server executable around the Lean-generated qrig core.
 *
 * Protocol (stdin -> stdout), repeated until EOF:
 *   request : "<cmd>\n<len>\n" followed by <len> bytes of argument
 *   response: "<len>\n" followed by <len> bytes of result
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(_WIN32) || defined(_WIN64)
#include <fcntl.h>
#include <io.h>
#endif

extern int qrig_init(void);
extern char *qrig_call_c(const char *cmd, const char *arg);
extern void qrig_free(char *p);

static int read_line(char *buf, size_t cap) {
  if (!fgets(buf, (int)cap, stdin)) return 0;
  size_t n = strlen(buf);
  while (n > 0 && (buf[n - 1] == '\n' || buf[n - 1] == '\r')) {
    buf[--n] = 0;
  }
  return 1;
}

int main(int argc, char **argv) {
#if defined(_WIN32) || defined(_WIN64)
  _setmode(_fileno(stdin), _O_BINARY);
  _setmode(_fileno(stdout), _O_BINARY);
#endif
  if (qrig_init() != 0) { fprintf(stderr, "qrig: initialisation failed\n"); return 1; }
  if (argc == 3) { /* one-shot mode: qrig-core <cmd> <arg> */
    char *r = qrig_call_c(argv[1], argv[2]);
    if (!r) return 1;
    puts(r);
    qrig_free(r);
    return 0;
  }
  char cmd[256], lenbuf[64];
  while (read_line(cmd, sizeof cmd)) {
    if (!read_line(lenbuf, sizeof lenbuf)) break;
    size_t len = strtoull(lenbuf, NULL, 10);
    char *arg = (char *)malloc(len + 1);
    if (!arg) return 1;
    if (len > 0 && fread(arg, 1, len, stdin) != len) { free(arg); break; }
    arg[len] = 0;
    char *r = qrig_call_c(cmd, arg);
    free(arg);
    if (!r) { printf("%d\n", 0); fflush(stdout); continue; }
    size_t rl = strlen(r);
    printf("%zu\n", rl);
    fwrite(r, 1, rl, stdout);
    fflush(stdout);
    qrig_free(r);
  }
  return 0;
}
