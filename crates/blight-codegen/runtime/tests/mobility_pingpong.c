/* mobility_pingpong.c — two-PROCESS proof for P5 code mobility (roadmap Wave 10): a closure crosses
 * a REAL loopback TCP socket between two independently-running OS processes running this SAME
 * compiled binary, and is applied on the receiving side to produce the identical result an
 * in-process call would.
 *
 * This is the C-runtime-level analogue of `blight-net`'s `pingpong.rs` (which proves the Actor
 * data-only transport crosses a real process boundary) but exercises the *_mobile serializer
 * (serialize.c's P5 extension) instead of the data-only one: `bl_value_serialize_mobile`/
 * `bl_value_deserialize_mobile`. Both roles are ONE executable (argv[1] selects the role), so
 * `bl_binary_id` is trivially identical between the two processes — they really are the same binary
 * (down to the same inode), not merely built from the same source twice.
 *
 * Protocol, over one TCP connection (pong listens, ping connects):
 *   pong: bind an ephemeral loopback port, print "PORT <p>" (the harness reads this to find pong),
 *         accept one connection, read a length-prefixed mobile blob, deserialize it (must be a
 *         BL_CLOSURE over the registered `succ_fn`), APPLY it to Int(41) via the ordinary two-arg
 *         calling convention every lifted function shares, mobile-serialize the Int result, and
 *         write it back length-prefixed. Exits 0 iff the received value really was a closure (not
 *         merely accepted-but-wrong) and the applied result is Int(42).
 *   ping: connect to the given port, build a closure over `succ_fn` (zero captures), mobile-serialize
 *         and send it, then read back pong's length-prefixed reply and deserialize it. Exits 0 iff
 *         the reply is Int(42).
 *
 * Both print a final "PINGPONG_MOBILITY_OK <role> <n>" line on success (checked by the Rust process
 * harness in `runtime.rs`), so a silent wrong-answer exit can't be mistaken for success.
 */
#include "blight_rt.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>

/* The two-argument calling convention every lifted top-level function shares (env, arg) -> result;
 * mirrors `effects.c`'s identically-named, identically-scoped local typedef (`bl_app_global`). */
typedef BlValue (*BlFn2)(BlValue env, BlValue arg);

static BlValue succ_fn(BlValue env, BlValue arg) {
  (void)env;
  return bl_int(bl_int_val(arg) + 1);
}

static void *g_table[] = { (void *)succ_fn };

/* A real `blight build` binary derives `bl_binary_id` from its function-name list at compile time
 * (`driver.rs`'s `fnv1a_binary_id`). This hand-written test has no such list to hash — and does not
 * need one, since BOTH roles below are literally the same already-compiled executable (spawned
 * twice with a different argv[1]), so any fixed constant both agree on already demonstrates the
 * "same binary identity" property `bl_binary_id` exists to check. */
#define TEST_BINARY_ID 0xA11CE5EED5A11CE5ULL

static void write_all(int fd, const void *buf, size_t n) {
  const unsigned char *p = (const unsigned char *)buf;
  size_t off = 0;
  while (off < n) {
    ssize_t w = write(fd, p + off, n - off);
    if (w <= 0) { perror("write"); exit(1); }
    off += (size_t)w;
  }
}

static void read_all(int fd, void *buf, size_t n) {
  unsigned char *p = (unsigned char *)buf;
  size_t off = 0;
  while (off < n) {
    ssize_t r = read(fd, p + off, n - off);
    if (r <= 0) { fprintf(stderr, "read: peer closed or errored before %zu bytes\n", n); exit(1); }
    off += (size_t)r;
  }
}

static void send_blob(int fd, const void *blob, size_t len) {
  uint32_t n = (uint32_t)len;
  write_all(fd, &n, sizeof(n));
  write_all(fd, blob, len);
}

static void *recv_blob(int fd, size_t *out_len) {
  uint32_t n;
  read_all(fd, &n, sizeof(n));
  void *buf = malloc(n);
  if (!buf) { fprintf(stderr, "recv_blob: OOM\n"); exit(1); }
  read_all(fd, buf, n);
  *out_len = n;
  return buf;
}

static int run_pong(void) {
  int listen_fd = socket(AF_INET, SOCK_STREAM, 0);
  if (listen_fd < 0) { perror("socket"); return 1; }
  int opt = 1;
  setsockopt(listen_fd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));
  struct sockaddr_in addr;
  memset(&addr, 0, sizeof(addr));
  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  addr.sin_port = 0;
  if (bind(listen_fd, (struct sockaddr *)&addr, sizeof(addr)) != 0) { perror("bind"); return 1; }
  socklen_t alen = sizeof(addr);
  if (getsockname(listen_fd, (struct sockaddr *)&addr, &alen) != 0) { perror("getsockname"); return 1; }
  printf("PORT %d\n", (int)ntohs(addr.sin_port));
  fflush(stdout);
  if (listen(listen_fd, 1) != 0) { perror("listen"); return 1; }
  int fd = accept(listen_fd, NULL, NULL);
  if (fd < 0) { perror("accept"); return 1; }

  size_t len = 0;
  void *blob = recv_blob(fd, &len);
  BlValue v = bl_value_deserialize_mobile(blob, len);
  free(blob);
  if (v == NULL || bl_obj_tag(v) != BL_CLOSURE) {
    fprintf(stderr, "pong: expected a closure, got %s\n",
            v ? "a non-closure value" : "NULL (rejected)");
    return 1;
  }

  void *fn = (void *)(uintptr_t)bl_obj_aux(v);
  BlValue arg = bl_int(41);
  BlValue result = ((BlFn2)fn)(NULL, arg);
  int64_t n = bl_int_val(result);

  size_t out_len = 0;
  void *out_blob = bl_value_serialize_mobile(result, &out_len);
  if (!out_blob) { fprintf(stderr, "pong: failed to serialize reply\n"); return 1; }
  send_blob(fd, out_blob, out_len);
  free(out_blob);
  close(fd);
  close(listen_fd);

  if (n != 42) {
    fprintf(stderr, "pong: applying the received closure gave %lld, expected 42\n", (long long)n);
    return 1;
  }
  printf("PINGPONG_MOBILITY_OK pong %lld\n", (long long)n);
  fflush(stdout);
  return 0;
}

static int run_ping(int port) {
  int fd = socket(AF_INET, SOCK_STREAM, 0);
  if (fd < 0) { perror("socket"); return 1; }
  struct sockaddr_in addr;
  memset(&addr, 0, sizeof(addr));
  addr.sin_family = AF_INET;
  addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  addr.sin_port = htons((uint16_t)port);
  int connected = 0;
  for (int i = 0; i < 200; i++) {
    if (connect(fd, (struct sockaddr *)&addr, sizeof(addr)) == 0) { connected = 1; break; }
    usleep(10000);
  }
  if (!connected) { fprintf(stderr, "ping: could not connect to 127.0.0.1:%d\n", port); return 1; }

  BlValue clo = bl_alloc(BL_CLOSURE, 0, (uint64_t)(uintptr_t)succ_fn);
  size_t len = 0;
  void *blob = bl_value_serialize_mobile(clo, &len);
  if (!blob) { fprintf(stderr, "ping: failed to serialize the closure\n"); return 1; }
  send_blob(fd, blob, len);
  free(blob);

  size_t reply_len = 0;
  void *reply_blob = recv_blob(fd, &reply_len);
  BlValue reply = bl_value_deserialize_mobile(reply_blob, reply_len);
  free(reply_blob);
  close(fd);
  if (reply == NULL) { fprintf(stderr, "ping: reply blob was rejected\n"); return 1; }
  int64_t n = bl_int_val(reply);
  if (n != 42) { fprintf(stderr, "ping: got %lld back, expected 42\n", (long long)n); return 1; }
  printf("PINGPONG_MOBILITY_OK ping %lld\n", (long long)n);
  fflush(stdout);
  return 0;
}

int main(int argc, char **argv) {
  bl_gc_init(1 * 1024 * 1024);
  bl_stack_init();
  bl_code_table_register(g_table, sizeof(g_table) / sizeof(g_table[0]), TEST_BINARY_ID);

  if (argc >= 2 && strcmp(argv[1], "pong") == 0) return run_pong();
  if (argc >= 3 && strcmp(argv[1], "ping") == 0) return run_ping(atoi(argv[2]));
  fprintf(stderr, "usage: %s (pong | ping <port>)\n", argv[0]);
  return 2;
}
