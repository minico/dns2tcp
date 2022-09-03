#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <assert.h>
#include <syslog.h>
#include <ctype.h>
#include <stdbool.h>
#include <string.h>
#include <time.h>
#include <errno.h>
#include <signal.h>
#include <unistd.h>
#include <fcntl.h>
#include <arpa/inet.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include "libev/ev.h"
#undef _GNU_SOURCE


#define DNS2TCP_VER "dns2tcp v1.1.0"
#define ENABLE_DUMP 


#ifndef IPV6_V6ONLY
  #define IPV6_V6ONLY 26
#endif
#ifndef SO_REUSEPORT
  #define SO_REUSEPORT 15
#endif
#ifndef TCP_QUICKACK
  #define TCP_QUICKACK 12
#endif
#ifndef TCP_SYNCNT
  #define TCP_SYNCNT 7
#endif
#ifndef MSG_FASTOPEN
  #define MSG_FASTOPEN 0x20000000
#endif


#define IP4STRLEN INET_ADDRSTRLEN /* ipv4addr max strlen */
#define IP6STRLEN INET6_ADDRSTRLEN /* ipv6addr max strlen */
#define PORTSTRLEN 6 /* "65535", include the null character */
#define UDPDGRAM_MAXSIZ 1472 /* mtu:1500 - iphdr:20 - udphdr:8 */


typedef uint16_t portno_t; /* 16bit */
typedef struct sockaddr_in  skaddr4_t;
typedef struct sockaddr_in6 skaddr6_t;


#define IF_VERBOSE if (g_verbose)

#define MAX_LOG_LEN 1024

#define LOGINF(fmt, ...)\
    do {\
        char buf[MAX_LOG_LEN] = {0};\
        struct tm *tm = localtime(&(time_t){time(NULL)});\
        snprintf(buf, MAX_LOG_LEN - 1, "%04d-%02d-%02d %02d:%02d:%02d INF:" fmt "\n", \
                tm->tm_year + 1900, tm->tm_mon + 1, tm->tm_mday,\
                tm->tm_hour, tm->tm_min, tm->tm_sec,\
                ##__VA_ARGS__);\
        printf("%s", buf);\
        syslog(LOG_INFO|LOG_USER,"%s", buf);\
    } while (0)


#define LOGERR(fmt, ...)                                                    \
    do {                                                                    \
        struct tm *tm = localtime(&(time_t){time(NULL)});                   \
        printf("\e[1;35m%04d-%02d-%02d %02d:%02d:%02d ERR:\e[0m " fmt "\n", \
                tm->tm_year + 1900, tm->tm_mon + 1, tm->tm_mday,            \
                tm->tm_hour,        tm->tm_min,     tm->tm_sec,             \
                ##__VA_ARGS__);                                             \
        syslog(LOG_ERR|LOG_USER,"[%s](%d)" fmt , __func__, __LINE__, ##__VA_ARGS__);\
    } while (0)


void hexdump(void *pSrc, int len) {
    unsigned char *line;
    int i;
    int thisline;
    int offset;


    line = (unsigned char *)pSrc;
    offset = 0;


    while (offset < len) {
        printf("%04x ", offset);
        thisline = len - offset;




        if (thisline > 16)
        {
            thisline = 16;
        }




        for (i = 0; i < thisline; i++)
        {
            printf("%02x ", line[i]);
        }




        for (; i < 16; i++)
        {
            printf("   ");
        }




        for (i = 0; i < thisline; i++)
        {
            printf("%c", (line[i] >= 0x20 && line[i] < 0x7f) ? line[i] : '.');
        }




        printf("\n");
        offset += thisline;
        line += thisline;
    }
}


typedef struct {
    evio_t    watcher;
    uint8_t   buffer[2 + UDPDGRAM_MAXSIZ]; /* msglen(16bit) + msgbuf */
    uint16_t  nrcvsnd;
    skaddr6_t srcaddr;
} tcpwatcher_t;


enum {
    OPT_IPV6_V6ONLY = 1 << 0,
    OPT_REUSE_PORT  = 1 << 1,
    OPT_QUICK_ACK   = 1 << 2,
    OPT_FAST_OPEN   = 1 << 3,
    OPT_IPV4_ONLY   = 1 << 4,
};


static bool       g_verbose                 = false;
static uint8_t    g_options                 = 0;
static uint8_t    g_syn_maxcnt              = 0;
static int        g_udp_sockfd              = -1;
static char       g_listen_ipstr[IP6STRLEN] = {0};
static portno_t   g_listen_portno           = 0;
static skaddr6_t  g_listen_skaddr           = {0};
static char       g_remote_ipstr[IP6STRLEN] = {0};
static portno_t   g_remote_portno           = 0;
static skaddr6_t  g_remote_skaddr           = {0};
static char       g_ipstr_buf[IP6STRLEN]    = {0};


static void udp_recvmsg_cb(evloop_t *evloop, evio_t *watcher, int events);
static void tcp_connect_cb(evloop_t *evloop, evio_t *watcher, int events);
static void tcp_sendmsg_cb(evloop_t *evloop, evio_t *watcher, int events);
static void tcp_recvmsg_cb(evloop_t *evloop, evio_t *watcher, int events);


static void set_nonblock(int sockfd) {
    int flags = fcntl(sockfd, F_GETFL, 0);
    if (flags < 0) {
        LOGERR("[set_nonblock] fcntl(%d, F_GETFL): (%d) %s", sockfd, errno, strerror(errno));
        exit(errno);
    }
    if (fcntl(sockfd, F_SETFL, flags | O_NONBLOCK) < 0) {
        LOGERR("[set_nonblock] fcntl(%d, F_SETFL): (%d) %s", sockfd, errno, strerror(errno));
        exit(errno);
    }
}


static void set_ipv6only(int sockfd) {
    if (setsockopt(sockfd, IPPROTO_IPV6, IPV6_V6ONLY, &(int){1}, sizeof(int)) < 0) {
        LOGERR("[set_ipv6only] setsockopt(%d, IPV6_V6ONLY): (%d) %s", sockfd, errno, strerror(errno));
        exit(errno);
    }
}


static void set_reuseaddr(int sockfd) {
    if (setsockopt(sockfd, SOL_SOCKET, SO_REUSEADDR, &(int){1}, sizeof(int)) < 0) {
        LOGERR("[set_reuseaddr] setsockopt(%d, SO_REUSEADDR): (%d) %s", sockfd, errno, strerror(errno));
        exit(errno);
    }
}


static void set_reuseport(int sockfd) {
    if (setsockopt(sockfd, SOL_SOCKET, SO_REUSEPORT, &(int){1}, sizeof(int)) < 0) {
        LOGERR("[set_reuseport] setsockopt(%d, SO_REUSEPORT): (%d) %s", sockfd, errno, strerror(errno));
        exit(errno);
    }
}


static void set_nodelay(int sockfd) {
    if (setsockopt(sockfd, IPPROTO_TCP, TCP_NODELAY, &(int){1}, sizeof(int)) < 0) {
        LOGERR("[set_nodelay] setsockopt(%d, TCP_NODELAY): (%d) %s", sockfd, errno, strerror(errno));
        exit(errno);
    }
}


static void set_quickack(int sockfd) {
    if (setsockopt(sockfd, IPPROTO_TCP, TCP_QUICKACK, &(int){1}, sizeof(int)) < 0) {
        LOGERR("[set_quickack] setsockopt(%d, TCP_QUICKACK): (%d) %s", sockfd, errno, strerror(errno));
        exit(errno);
    }
}


static void set_syncnt(int sockfd, int syncnt) {
    if (setsockopt(sockfd, IPPROTO_TCP, TCP_SYNCNT, &syncnt, sizeof(syncnt)) < 0) {
        LOGERR("[set_syncnt] setsockopt(%d, TCP_SYNCNT): (%d) %s", sockfd, errno, strerror(errno));
        exit(errno);
    }
}


static int get_ipstr_family(const char *ipstr) {
    if (!ipstr) return -1; /* invalid */
    uint8_t ipaddr[16]; /* 16-bytes */
    if (inet_pton(AF_INET, ipstr, &ipaddr) == 1) {
        return AF_INET;
    } else if (inet_pton(AF_INET6, ipstr, &ipaddr) == 1) {
        return AF_INET6;
    } else {
        return -1; /* invalid */
    }
}


static void build_socket_addr(int ipfamily, void *skaddr, const char *ipstr, portno_t portno) {
    if (ipfamily == AF_INET) {
        skaddr4_t *addr = skaddr;
        addr->sin_family = AF_INET;
        inet_pton(AF_INET, ipstr, &addr->sin_addr);
        addr->sin_port = htons(portno);
    } else {
        skaddr6_t *addr = skaddr;
        addr->sin6_family = AF_INET6;
        inet_pton(AF_INET6, ipstr, &addr->sin6_addr);
        addr->sin6_port = htons(portno);
    }
}


static void parse_socket_addr(const void *skaddr, char *ipstr, portno_t *portno) {
    if (((skaddr4_t *)skaddr)->sin_family == AF_INET) {
        const skaddr4_t *addr = skaddr;
        inet_ntop(AF_INET, &addr->sin_addr, ipstr, IP4STRLEN);
        *portno = ntohs(addr->sin_port);
    } else {
        const skaddr6_t *addr = skaddr;
        inet_ntop(AF_INET6, &addr->sin6_addr, ipstr, IP6STRLEN);
        *portno = ntohs(addr->sin6_port);
    }
}


static void print_command_help(void) {
    printf("usage: dns2tcp <-L listen> <-R remote> [-s syncnt] [-6rafvVh]\n"
           " -L <ip#port>            udp listen address, this is required\n"
           " -R <ip#port>            tcp remote address, this is required\n"
           " -s <syncnt>             set TCP_SYNCNT(max) for remote socket\n"
           " -4                      request for type A(ipv4) only, ignore AAAA(ipv6) reqeust\n"
           " -6                      enable IPV6_V6ONLY for listen socket\n"
           " -r                      enable SO_REUSEPORT for listen socket\n"
           " -a                      enable TCP_QUICKACK for remote socket\n"
           " -f                      enable TCP_FASTOPEN for remote socket\n"
           " -v                      print verbose log, default: <disabled>\n"
           " -V                      print version number of dns2tcp and exit\n"
           " -h                      print help information of dns2tcp and exit\n"
           "bug report: https://github.com/zfl9/dns2tcp. email: zfl9.com@gmail.com\n"
    );
}


static void parse_address_opt(char *ip_port_str, bool is_listen_addr) {
    printf("[parse_address_opt]ip_port_str:%s is_listen_addr:%d\n", ip_port_str, is_listen_addr);
    const char *opt_name = is_listen_addr ? "listen" : "remote";


    char *portstr = strchr(ip_port_str, '#');
    if (!portstr) {
        printf("[parse_address_opt] %s port not provided\n", opt_name);
        goto PRINT_HELP_AND_EXIT;
    }
    if (portstr == ip_port_str) {
        printf("[parse_address_opt] %s addr not provided\n", opt_name);
        goto PRINT_HELP_AND_EXIT;
    }
    if (portstr == ip_port_str + strlen(ip_port_str) - 1) {
        printf("[parse_address_opt] %s port not provided\n", opt_name);
        goto PRINT_HELP_AND_EXIT;
    }


    *portstr = 0; ++portstr;
    if (strlen(portstr) + 1 > PORTSTRLEN) {
        printf("[parse_address_opt] %s port is invalid: %s\n", opt_name, portstr);
        goto PRINT_HELP_AND_EXIT;
    }
    portno_t portno = strtoul(portstr, NULL, 10);
    if (portno == 0) {
        printf("[parse_address_opt] %s port is invalid: %s\n", opt_name, portstr);
        goto PRINT_HELP_AND_EXIT;
    }


    const char *ipstr = ip_port_str;
    if (strlen(ipstr) + 1 > IP6STRLEN) {
        printf("[parse_address_opt] %s addr is invalid: %s\n", opt_name, ipstr);
        goto PRINT_HELP_AND_EXIT;
    }
    int ipfamily = get_ipstr_family(ipstr);
    if (ipfamily == -1) {
        printf("[parse_address_opt] %s addr is invalid: %s\n", opt_name, ipstr);
        goto PRINT_HELP_AND_EXIT;
    }


    if (is_listen_addr) {
        strcpy(g_listen_ipstr, ipstr);
        g_listen_portno = portno;
        build_socket_addr(ipfamily, &g_listen_skaddr, ipstr, portno);
    } else {
        strcpy(g_remote_ipstr, ipstr);
        g_remote_portno = portno;
        build_socket_addr(ipfamily, &g_remote_skaddr, ipstr, portno);
    }
    return;


PRINT_HELP_AND_EXIT:
    print_command_help();
    exit(1);
}


static void parse_command_args(int argc, char *argv[]) {
    char opt_listen_addr[IP6STRLEN + PORTSTRLEN] = {0};
    char opt_remote_addr[IP6STRLEN + PORTSTRLEN] = {0};


    opterr = 0;
    int shortopt = -1;
    const char *optstr = "L:R:s:46rafvVh";
    while ((shortopt = getopt(argc, argv, optstr)) != -1) {
        printf("[parse_command_args] shortopt: %d, optarg:%s\n", shortopt, optarg);
        switch (shortopt) {
            case 'L':
                if (strlen(optarg) + 1 > IP6STRLEN + PORTSTRLEN) {
                    printf("[parse_command_args] invalid listen addr: %s\n", optarg);
                    goto PRINT_HELP_AND_EXIT;
                }
                strcpy(opt_listen_addr, optarg);
                break;
            case 'R':
                if (strlen(optarg) + 1 > IP6STRLEN + PORTSTRLEN) {
                    printf("[parse_command_args] invalid remote addr: %s\n", optarg);
                    goto PRINT_HELP_AND_EXIT;
                }
                strcpy(opt_remote_addr, optarg);
                break;
            case 's':
                g_syn_maxcnt = strtoul(optarg, NULL, 10);
                if (g_syn_maxcnt == 0) {
                    printf("[parse_command_args] invalid tcp syn cnt: %s\n", optarg);
                    goto PRINT_HELP_AND_EXIT;
                }
                break;
            case '4':
                g_options |= OPT_IPV4_ONLY;
                break;
            case '6':
                g_options |= OPT_IPV6_V6ONLY;
                break;
            case 'r':
                g_options |= OPT_REUSE_PORT;
                break;
            case 'a':
                g_options |= OPT_QUICK_ACK;
                break;
            case 'f':
                g_options |= OPT_FAST_OPEN;
                break;
            case 'v':
                g_verbose = true;
                break;
            case 'V':
                printf(DNS2TCP_VER"\n");
                exit(0);
            case 'h':
                print_command_help();
                exit(0);
            case '?':
                if (!strchr(optstr, optopt)) {
                    printf("[parse_command_args] unknown option '-%c'\n", optopt);
                } else {
                    printf("[parse_command_args] missing optval '-%c'\n", optopt);
                }
                goto PRINT_HELP_AND_EXIT;
        }
    }


    if (strlen(opt_listen_addr) == 0) {
        printf("[parse_command_args] missing option: '-L'\n");
        goto PRINT_HELP_AND_EXIT;
    }
    if (strlen(opt_remote_addr) == 0) {
        printf("[parse_command_args] missing option: '-R'\n");
        goto PRINT_HELP_AND_EXIT;
    }


    parse_address_opt(opt_listen_addr, true);
    parse_address_opt(opt_remote_addr, false);
    return;


PRINT_HELP_AND_EXIT:
    print_command_help();
    exit(1);
}


int main(int argc, char *argv[]) {
    signal(SIGPIPE, SIG_IGN);
    setvbuf(stdout, NULL, _IOLBF, 256);
    parse_command_args(argc, argv);


    LOGINF("[main] udp listen addr: %s#%hu", g_listen_ipstr, g_listen_portno);
    LOGINF("[main] tcp remote addr: %s#%hu", g_remote_ipstr, g_remote_portno);
    if (g_syn_maxcnt) LOGINF("[main] enable TCP_SYNCNT:%hhu sockopt", g_syn_maxcnt);
    if (g_options & OPT_IPV4_ONLY) LOGINF("[main] enable IPV4_ONLY");
    if (g_options & OPT_IPV6_V6ONLY) LOGINF("[main] enable IPV6_V6ONLY sockopt");
    if (g_options & OPT_REUSE_PORT) LOGINF("[main] enable SO_REUSEPORT sockopt");
    if (g_options & OPT_QUICK_ACK) LOGINF("[main] enable TCP_QUICKACK sockopt");
    if (g_options & OPT_FAST_OPEN) LOGINF("[main] enable TCP_FASTOPEN sockopt");
    IF_VERBOSE LOGINF("[main] verbose mode, affect performance");


    g_udp_sockfd = socket(g_listen_skaddr.sin6_family, SOCK_DGRAM, 0);
    if (g_udp_sockfd < 0) {
        LOGERR("[main] create udp socket: (%d) %s", errno, strerror(errno));
        return errno;
    }


    set_nonblock(g_udp_sockfd);
    set_reuseaddr(g_udp_sockfd);
    if (g_options & OPT_REUSE_PORT) set_reuseport(g_udp_sockfd);
    if ((g_options & OPT_IPV6_V6ONLY) && g_listen_skaddr.sin6_family == AF_INET6) set_ipv6only(g_udp_sockfd);


    if (bind(g_udp_sockfd, (void *)&g_listen_skaddr, g_listen_skaddr.sin6_family == AF_INET ? sizeof(skaddr4_t) : sizeof(skaddr6_t)) < 0) {
        LOGERR("[main] bind udp address: (%d) %s", errno, strerror(errno));
        return errno;
    }


    evloop_t *evloop = ev_default_loop(0);
    evio_t *watcher = &(evio_t){0};
    ev_io_init(watcher, udp_recvmsg_cb, g_udp_sockfd, EV_READ);
    ev_io_start(evloop, watcher);


    ev_run(evloop, 0);
    return 0;
}


static void udp_recvmsg_cb(evloop_t *evloop, evio_t *watcher __attribute__((unused)), int events __attribute__((unused))) {
    tcpwatcher_t *tcpw = malloc(sizeof(*tcpw));
    ssize_t nrecv = recvfrom(g_udp_sockfd, (void *)tcpw->buffer + 2, UDPDGRAM_MAXSIZ, 0, (void *)&tcpw->srcaddr, &(socklen_t){sizeof(tcpw->srcaddr)});
    if (nrecv < 0) {
        if (errno != EAGAIN && errno != EWOULDBLOCK) {
            LOGERR("[udp_recvmsg_cb] recv from udp socket: (%d) %s", errno, strerror(errno));
        }
        goto FREE_TCP_WATCHER;
    }
    IF_VERBOSE {
        portno_t portno;
        parse_socket_addr(&tcpw->srcaddr, g_ipstr_buf, &portno);
        LOGINF("[udp_recvmsg_cb] recv from %s#%hu, nrecv:%zd", g_ipstr_buf, portno, nrecv);
    }
    uint16_t *msglen_ptr = (void *)tcpw->buffer;

#if 1
    char domain[256] = {0};
    strcpy(domain, (const char*)tcpw->buffer + 2 + 12);
    char* ch = domain + 1; //skip the length field
    while(*ch != '\0') {
        if (!isprint(*ch)) {
            *ch = '.';//replace other length field to .
        }
        ++ch;
    }
    uint16_t req_type = ntohs(*(uint16_t*)(tcpw->buffer + 2 + 12 + strlen(domain) + 1));
    IF_VERBOSE LOGINF("request dns for:%s with type:%s\n", domain, req_type == 1 ? "A" : "AAAA");
#endif

    *msglen_ptr = htons(nrecv); /* msg length */
    nrecv += 2; /* msglen + msgbuf */
    tcpw->nrcvsnd = 0;

#ifdef ENABLE_DUMP
    hexdump(tcpw->buffer, nrecv);
#endif

    int sockfd = socket(g_remote_skaddr.sin6_family, SOCK_STREAM, 0);
    if (sockfd < 0) {
        LOGERR("[udp_recvmsg_cb] create tcp socket: (%d) %s", errno, strerror(errno));
        goto FREE_TCP_WATCHER;
    }
    set_nonblock(sockfd);
    set_reuseaddr(sockfd);
    set_nodelay(sockfd);
    if (g_syn_maxcnt) set_syncnt(sockfd, g_syn_maxcnt);
    if (g_options & OPT_QUICK_ACK) set_quickack(sockfd);


    bool tfo_succ = false;
    if (g_options & OPT_FAST_OPEN) {
        ssize_t nsend = sendto(sockfd, tcpw->buffer, nrecv, MSG_FASTOPEN, (void *)&g_remote_skaddr, g_remote_skaddr.sin6_family == AF_INET ? sizeof(skaddr4_t) : sizeof(skaddr6_t));
        if (nsend < 0) {
            if (errno != EINPROGRESS) {
                LOGERR("[udp_recvmsg_cb] connect to %s#%hu: (%d) %s", g_remote_ipstr, g_remote_portno, errno, strerror(errno));
                goto CLOSE_TCP_SOCKFD;
            }
            IF_VERBOSE LOGINF("[udp_recvmsg_cb] try to connect to %s#%hu", g_remote_ipstr, g_remote_portno);
        } else {
            tfo_succ = true;
            tcpw->nrcvsnd = nsend;
            IF_VERBOSE LOGINF("[udp_recvmsg_cb] tcp_fastopen connect, nsend:%zd", nsend);
        }
    } else {
        if (connect(sockfd, (void *)&g_remote_skaddr, g_remote_skaddr.sin6_family == AF_INET ? sizeof(skaddr4_t) : sizeof(skaddr6_t)) < 0 && errno != EINPROGRESS) {
            LOGERR("[udp_recvmsg_cb] connect to %s#%hu: (%d) %s", g_remote_ipstr, g_remote_portno, errno, strerror(errno));
            goto CLOSE_TCP_SOCKFD;
        }
        IF_VERBOSE LOGINF("[udp_recvmsg_cb] try to connect to %s#%hu", g_remote_ipstr, g_remote_portno);
    }


    if (tfo_succ && tcpw->nrcvsnd >= nrecv) {
        tcpw->nrcvsnd = 0; /* reset to zero for recv data */
        ev_io_init((evio_t *)tcpw, tcp_recvmsg_cb, sockfd, EV_READ);
    } else {
        ev_io_init((evio_t *)tcpw, tfo_succ ? tcp_sendmsg_cb : tcp_connect_cb, sockfd, EV_WRITE);
    }
    ev_io_start(evloop, (evio_t *)tcpw);
    return;


CLOSE_TCP_SOCKFD:
    close(sockfd);
FREE_TCP_WATCHER:
    free(tcpw);
}


static void tcp_connect_cb(evloop_t *evloop, evio_t *watcher, int events __attribute__((unused))) {
    if (getsockopt(watcher->fd, SOL_SOCKET, SO_ERROR, &errno, &(socklen_t){sizeof(errno)}) < 0 || errno) {
        LOGERR("[tcp_connect_cb] connect to %s#%hu: (%d) %s", g_remote_ipstr, g_remote_portno, errno, strerror(errno));
        ev_io_stop(evloop, watcher);
        close(watcher->fd);
        free(watcher);
        return;
    }
    IF_VERBOSE LOGINF("[tcp_connect_cb] connect to %s#%hu succeed", g_remote_ipstr, g_remote_portno);
    ev_set_cb(watcher, tcp_sendmsg_cb);
    ev_invoke(evloop, watcher, EV_WRITE);
}


static void tcp_sendmsg_cb(evloop_t *evloop, evio_t *watcher, int events __attribute__((unused))) {
    tcpwatcher_t *tcpw = (void *)watcher;
    uint16_t *msglen_ptr = (void *)tcpw->buffer;
    uint16_t datalen = 2 + ntohs(*msglen_ptr);
    ssize_t nsend = send(watcher->fd, (void *)tcpw->buffer + tcpw->nrcvsnd, datalen - tcpw->nrcvsnd, 0);
    if (nsend < 0) {
        if (errno == EAGAIN || errno == EWOULDBLOCK) return;
        LOGERR("[tcp_sendmsg_cb] send to %s#%hu: (%d) %s", g_remote_ipstr, g_remote_portno, errno, strerror(errno));
        ev_io_stop(evloop, watcher);
        close(watcher->fd);
        free(watcher);
        return;
    }
    IF_VERBOSE LOGINF("[tcp_sendmsg_cb] send to %s#%hu, nsend:%zd", g_remote_ipstr, g_remote_portno, nsend);
    tcpw->nrcvsnd += nsend;
    if (tcpw->nrcvsnd >= datalen) {
        tcpw->nrcvsnd = 0; /* reset to zero for recv data */
        ev_io_stop(evloop, watcher);
        ev_io_init(watcher, tcp_recvmsg_cb, watcher->fd, EV_READ);
        ev_io_start(evloop, watcher);
    }
}


int check_ipv6_addr(char* answer) {
    uint16_t type = ntohs(*(uint16_t*)(answer+ 2));
    uint16_t len = ntohs(*(uint16_t*)(answer+ 10));
    IF_VERBOSE LOGINF("check_ipv6_addr answer:%p, type:%d, len:%d", answer, type, len);
    if (type == 28) {// IPv6 address
        assert(len == 16);
        char ip[64] = {0};
        int cur_pos = 0;
        for (int i=0; i<len; i++) {
            sprintf(ip + cur_pos, "%02x:", answer[12 + i]);
            cur_pos += 2;
            if (i % 2 == 1 && i != len - 1) {
                sprintf(ip + cur_pos, "%s", ":");
                cur_pos += 1;
            }
        }
        ip[cur_pos] = '\0';
        
        char cmd[256] = {0};
        sprintf(cmd, "fping -c1 -t300 %s > /dev/null 2>&1", ip);
        int res = system(cmd);
        if (res == 0){
            IF_VERBOSE LOGINF("%s is active", ip);
            // do nothing, return the original info
        } else {
            // replace the fake ip ::2
            IF_VERBOSE LOGINF("%s is not active", ip);
            for (int i=0; i<len; i++) {
                answer[12 + i] = 0;
            }
            answer[12 + len -1] = 0x02;
        }
    }
    return len + 12;
}

static void tcp_recvmsg_cb(evloop_t *evloop, evio_t *watcher, int events __attribute__((unused))) {
    tcpwatcher_t *tcpw = (void *)watcher;
    void *buffer = tcpw->buffer;

    ssize_t nrecv = recv(watcher->fd, buffer + tcpw->nrcvsnd, 2 + UDPDGRAM_MAXSIZ - tcpw->nrcvsnd, 0);
    if (nrecv < 0) {
        if (errno == EAGAIN || errno == EWOULDBLOCK) return;
        LOGERR("[tcp_recvmsg_cb] recv from %s#%hu: (%d) %s", g_remote_ipstr, g_remote_portno, errno, strerror(errno));
        goto FREE_TCP_WATCHER;
    }
    if (nrecv == 0) {
        LOGERR("[tcp_recvmsg_cb] recv from %s#%hu: connection is closed", g_remote_ipstr, g_remote_portno);
        goto FREE_TCP_WATCHER;
    }
    tcpw->nrcvsnd += nrecv;
    IF_VERBOSE LOGINF("[tcp_recvmsg_cb] recv from %s#%hu, nrecv:%zd", g_remote_ipstr, g_remote_portno, nrecv);
    if (tcpw->nrcvsnd < 2 || tcpw->nrcvsnd < 2 + ntohs(*(uint16_t *)buffer)) return;

#ifdef ENABLE_DUMP
    hexdump(tcpw->buffer, nrecv);
#endif

#if 1
    char domain[256] = {0};
    strcpy(domain, (const char*)tcpw->buffer + 2 + 12);
    char* ch = domain + 1;
    while(*ch != '\0') {
        if (!isprint(*ch)) {
            *ch = '.';
        }
        ++ch;
    }
    uint16_t rr_cnt = ntohs(*(uint16_t*)(tcpw->buffer + 2 + 6));
    uint16_t authority_rr_cnt = ntohs(*(uint16_t*)(tcpw->buffer + 2 + 8));
    uint16_t additional_rr_cnt = ntohs(*(uint16_t*)(tcpw->buffer + 2 + 10));
    // add one extra char for '\0' after domain name
    uint16_t req_type = ntohs(*(uint16_t*)(tcpw->buffer + 2 + 12 + strlen(domain) + 1));

    IF_VERBOSE LOGINF("response dns for:%s with type:%d\n, buffer:%p", domain, req_type, tcpw->buffer);
    IF_VERBOSE LOGINF("rr_cnt:%d, authority_rr_cnt:%d, additional_rr_cnt:%d", rr_cnt, authority_rr_cnt, additional_rr_cnt);

    char* answer = (char*)tcpw->buffer + 2 + 12 + strlen(domain) + 1 + 4;
    for (int i=0; i<rr_cnt; i++) {
        answer += check_ipv6_addr(answer);
    }
#if 0
    for (int i=0; i<authority_rr_cnt; i++) {
        answer += check_ipv6_addr(answer);
    }
    for (int i=0; i<additional_rr_cnt; i++) {
        answer += check_ipv6_addr(answer);
    }
#endif

    uint16_t msg_len = ntohs(*(uint16_t *)buffer);
#ifdef ENABLE_DUMP
    hexdump(tcpw->buffer + 2, msg_len);
#endif
    IF_VERBOSE LOGINF("buffer:%p, answer:%p, msg_len:%d", buffer, answer, msg_len);

    //assert(answer == buffer + 2 + msg_len);
#if 0
    if ((g_options & OPT_IPV4_ONLY && req_type == 28) && tcpw->buffer[9] > 0) {
        printf("ignore AAAA type response for:%s\n", domain);
        tcpw->buffer[9] = 1;
        tcpw->buffer[2 + 12 + strlen(domain) + 1 + 4 + 2 ] = 0;
        tcpw->buffer[2 + 12 + strlen(domain) + 1 + 4 + 2 + 1] = 0x1c;
        tcpw->buffer[2 + 12 + strlen(domain) + 1 + 4 + 2 + 2] = 0;
        tcpw->buffer[2 + 12 + strlen(domain) + 1 + 4 + 2 + 2 + 1] = 1;
        tcpw->buffer[2 + 12 + strlen(domain) + 1 + 4 + 2 + 4 + 4 + 1] = 16;
        tcpw->buffer[2 + 12 + strlen(domain) + 1 + 4 + 2 + 4 + 4 + 2 + 15] = 1;
        memset(tcpw->buffer + 2 + 12 + strlen(domain) + 1 + 4 + 2 + 4 + 4 + 2, 0, 15);
        msg_len = 12 + strlen(domain) + 1 + 4 + 2 + 4 + 4 + 2 + 16;
        tcpw->buffer[1] = msg_len;
    }
#endif
#endif


    const void *sendto_skaddr = &tcpw->srcaddr;
    socklen_t sendto_skaddrlen = tcpw->srcaddr.sin6_family == AF_INET ? sizeof(skaddr4_t) : sizeof(skaddr6_t);
    ssize_t nsend = sendto(g_udp_sockfd, buffer + 2, ntohs(*(uint16_t *)buffer), 0, sendto_skaddr, sendto_skaddrlen);
    if (nsend < 0) {
        portno_t portno;
        parse_socket_addr(&tcpw->srcaddr, g_ipstr_buf, &portno);
        LOGERR("[tcp_recvmsg_cb] send to %s#%hu: (%d) %s", g_ipstr_buf, portno, errno, strerror(errno));
    } else {
        IF_VERBOSE {
            portno_t portno;
            parse_socket_addr(&tcpw->srcaddr, g_ipstr_buf, &portno);
            LOGINF("[tcp_recvmsg_cb] send to %s#%hu, nsend:%zd", g_ipstr_buf, portno, nsend);
        }
    }
FREE_TCP_WATCHER:
    ev_io_stop(evloop, watcher);
    close(watcher->fd);
    free(watcher);
}
