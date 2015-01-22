// #include "ctl.h"
// Property: G( FG(ret==OK)  \/ added<=0 )

#include <stdio.h>
#define AF_INET 1
#define AF_INET6 2
#define AF_UNIX 3
#define IS_AF_UNIX(a) nondet()
#define IS_AF_UNIX(a) nondet()

#define HAVE_IPV6 1
#define HAVE_UNIX_SOCKETS 1
#define PG_SOMAXCONN 10
#define SOCK_STREAM 1
#define STATUS_ERROR 0
#define STATUS_OK 1
int closed;
int MaxBackends;
int __rho_1_;
int __rho_2_;
int __rho_3_;
int __rho_4_;
int __rho_5_;
int __rho_6_;
int __rho_7_;
int __rho_8_;
int __rho_9_;
int __rho_15_;
int __rho_16_;

//#define snprintf(a,b,c,d) nondet()
#define gettext(a) ""
#define ereport(a,b,c) nondet()
//int getaddrinfo_all(int a, int b, int c, int d) { 
#define listen(a,b) nondet()
#define snprintf(a,b,c,f) {}
#define errmsg(a,b,c,d) ()
#define errcode_for_socket_access() 1
//#define 
#define LOG 0
#define closesocket(a) { closed=1; }
#define __builtin___snprintf_chk(a,b,c,d,e,f) {}
#define __builtin___object_size(a,b) nondet()
#define socket(a,b,c) { return nondet(); }

/*postgresql-8.0.2/src/backend/libpq.c
 * StreamServerPort -- open a "listening" port to accept connections.
 *
 * Successfully opened sockets are added to the ListenSocket[] array,
 * at the first position that isn't -1.
 *
 * RETURNS: STATUS_OK or STATUS_ERROR
 */

int family;
char *hostName;
unsigned short portNumber;
char *unixSocketName;
int MaxListen;
int fd, err;
int maxconn;
int one;
int ret;
//char            portNumberStr[32];
//const char *familyDesc;
//char            familyDescBuf[64];
char       *service;
/* struct addrinfo *addrs = NULL, */
/*   *addr; */
/* struct addrinfo hint; */
int hint;
int                     listen_index;
int                     added;
int addr_ai_family;
int addr;
int MAXADDR;
int ListenSocket_OF_listen_index;
int ret;
char *sock_path;
int addrs;

unsigned int pc;
 inline int __phi() { return CAG(COR(CAF(CAG(CAP(ret==STATUS_OK))),CAP(added<=0))); }

// Property: G( FG(ret==OK)  \/ added<=0 )

 inline void init() {
  one = 1;
  listen_index = 0;
  added = 0;
  MAXADDR = nondet();
  addrs = nondet(); assume(addrs>=0);
  MaxBackends = nondet(); assume(MaxBackends>0);
  ret = nondet();
}

inline int body()
{
        /* Initialize hint structure */

#ifdef HAVE_UNIX_SOCKETS
        if (family == AF_UNIX)
        {
                /* Lock_AF_UNIX will also fill in sock_path. */
                /* if (Lock_AF_UNIX(portNumber, unixSocketName) != STATUS_OK) */
                /*         return STATUS_ERROR; */
                service = sock_path;
        }
        else
#endif   /* HAVE_UNIX_SOCKETS */
        {
	  //snprintf(1, sizeof(1), "%d", portNumber);
                service = 1;
        }

	__rho_9_ = nondet();
        ret = __rho_9_; // getaddrinfo_all(hostName, service, &hint, &addrs);
        if (ret>0 || addrs<=0)
        {
	  if (hostName>0) {
                        /* ereport(LOG, */
                        /*                 (errmsg("could not translate host name \"%s\", service \"%s\" to address: %s", */
                        /*                                 hostName, service, gai_strerror(ret)))); */
	  } else {
                        /* ereport(LOG, */
                        /*  (errmsg("could not translate service \"%s\" to address: %s", */
                        /*                  service, gai_strerror(ret)))); */
                /* if (addrs) */
                /*         freeaddrinfo_all(hint.ai_family, addrs); */
	  }
	  //ret = STATUS_ERROR;
	  //while(1) { int qqq; qqq=qqq;}
        }
	
	addr = addrs;
	while(1) {
	  if (!(addr < MAXADDR)) break;
	  //for (addr = addrs; addr < MAXADDR; addr++) //  = addr->ai_next)

	  __rho_2_ = nondet(); //IS_AF_UNIX(family);
	  __rho_3_ = nondet(); //IS_AF_UNIX(addr_ai_family);
	  if (__rho_2_<=0 && __rho_3_>0)
                {
                        /*
                         * Only set up a unix domain socket when they really asked for
                         * it.  The service/port is different in that case.
                         */
                        goto loc_continue;
                }

                /* See if there is still room to add 1 more socket. */
                while(1) //for (; listen_index < MaxListen; listen_index++)
                {
		  if(listen_index < MaxListen) break;

                        if (ListenSocket_OF_listen_index == -1)
                                break;
			listen_index++;
                }
                if (listen_index >= MaxListen)
                {
                        /* ereport(LOG, */
                        /*                 (errmsg("could not bind to all requested addresses: MAXLISTEN (%d) exceeded", */
                        /*                                 MaxListen))); */
                        break;
                }

                /* set up family name for possible error messages */
		  if(addr_ai_family==AF_INET) {
		    //gettext("IPv4");
		  } else if(addr_ai_family==AF_INET6) {
		    //gettext("IPv6");
		  } else if(addr_ai_family==AF_UNIX) {
		    //gettext("Unix");
		  } else {
		    //snprintf(1,/*familyDescBuf*/ 1, //sizeof(familyDescBuf),
		    //gettext("unrecognized address family %d"),
		    //addr_ai_family);
                                //familyDesc = familyDescBuf;
		  }
		  __rho_15_ = nondet();
		  fd = __rho_15_;
                if (fd>0) // socket(addr_ai_family, SOCK_STREAM, 0)) < 0)
                {
                        /* ereport(LOG, */
                        /*                 (errcode_for_socket_access(), */
                        /* /\* translator: %s is IPv4, IPv6, or Unix *\/ */
                        /*                  errmsg("could not create %s socket: %m", */
                        /*                                 familyDesc))); */
                        goto loc_continue;
                }

		__rho_4_ = nondet();
                if (__rho_4_>0) // !IS_AF_UNIX(addr_ai_family))
                {
		__rho_5_ = nondet();
		  if (__rho_5_>0) //(setsockopt(fd, SOL_SOCKET, SO_REUSEADDR,
		    //                       (char *) &one, sizeof(one))) == -1)
                        {
                                /* ereport(LOG, */
                                /*                 (errcode_for_socket_access(), */
                                /*                  errmsg("setsockopt(SO_REUSEADDR) failed: %m"))); */
                                /* closesocket(fd); */
                                goto loc_continue;
                        }
                }

#ifdef IPV6_V6ONLY
		__rho_6_ = nondet();
                if (__rho_6_>0) // addr_ai_family == AF_INET6)
                {
		__rho_7_ = nondet();
		  if (__rho_7_>0) // setsockopt(fd, IPPROTO_IPV6, IPV6_V6ONLY,
		    //                  (char *) &one, sizeof(one)) == -1)
		    {
                                /* ereport(LOG, */
                                /*                 (errcode_for_socket_access(), */
                                /*                  errmsg("setsockopt(IPV6_V6ONLY) failed: %m"))); */
                                //closesocket(fd);
                                goto loc_continue;
                        }
                }
#endif

                /*
                 * Note: This might fail on some OS's, like Linux older than
                 * 2.4.21-pre3, that don't have the IPV6_V6ONLY socket option, and
                 * map ipv4 addresses to ipv6.  It will show ::ffff:ipv4 for all
                 * ipv4 connections.
                 */
		__rho_1_= nondet();
                err = __rho_1_; // bind(fd, addr->ai_addr, addr->ai_addrlen);
                if (err < 0)
                {
                        /* ereport(LOG, */
                        /*                 (errcode_for_socket_access(), */
                        /* /\* translator: %s is IPv4, IPv6, or Unix *\/ */
                        /*                  errmsg("could not bind %s socket: %m", */
                        /*                                 familyDesc), */
                        /*                  (IS_AF_UNIX(addr_ai_family)) ? */
                        /*   errhint("Is another postmaster already running on port %d?" */
                        /*                   " If not, remove socket file \"%s\" and retry.", */
                        /*                   (int) portNumber, sock_path) : */
                        /*   errhint("Is another postmaster already running on port %d?" */
                        /*                   " If not, wait a few seconds and retry.", */
                        /*                   (int) portNumber))); */
                        //closesocket(fd);
                        goto loc_continue;
                }

#ifdef HAVE_UNIX_SOCKETS
                if (addr_ai_family == AF_UNIX)
                {
		  __rho_8_ = nondet();
		  if (__rho_8_ != STATUS_OK)
                        {
			  //closesocket(fd);
                                break;
                        }
                }
#endif

                /*
                 * Select appropriate accept-queue length limit.  PG_SOMAXCONN is
                 * only intended to provide a clamp on the request on platforms
                 * where an overly large request provokes a kernel error (are
                 * there any?).
                 */
                maxconn = MaxBackends * 2;
                if (maxconn > PG_SOMAXCONN)
                        maxconn = PG_SOMAXCONN;

		__rho_16_ = nondet();
                err = __rho_16_; // listen(fd, maxconn);
                if (err < 0)
                {

		  //closesocket(fd);
                } else {
		  ListenSocket_OF_listen_index = fd;
		  added++;
		}

	loc_continue:
		addr++;
	}

        //freeaddrinfo_all(hint.ai_family, addrs);
        if (added<=0) {
                ret = STATUS_ERROR;
		//goto L_return; //while(1) { int rrr; rrr=rrr; }
	} else {
	  ret = STATUS_OK;
	}
  while(1) { dummy=dummy; } L_return: return 0;

}

//inline int body() { }

 int main() { init(); body(); }
