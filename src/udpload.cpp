static char *version = "Version 1.0.12 - 10 August 2010";
/*
 * udpload - keep writing a wheelbarrow full of UDP packets.
 * Tool used for benchmarking network equipment. Great alternative to other 3rd party
 * performance tools which suffers from gratuitous CPU usage.
 *
 * Version 1.0.12 - Tuesday 10 August 2010
 *  - The nanosleep() change introduced in Version 1.0.11 can now be disabled:
 *    [ -t ] uses busy-wait (100% CPU load) accurate timing.
 *    Without it, you get your CPU back, but much less accurate timing.
 *
 *  - New option [ -R ] inserts a pre-canned RTP header into each packet,
 *    and increments the RTP Sequence Number.
 *
 *  - Corrected Usage() text descriptions of Server Mode -o and -s options.
 *
 *  - Usage() now also prints the version number (the one on line 1 above).
 *
 * Version 1.0.11 - Thursday 20 May 2010
 *  - Replaced shorttime() microsecond delay function with calls to nanosleep().
 *    On Solaris, this may require linking with "-lrt" real-time library.
 *
 * Version 1.0.10 - Friday 7 May 2009
 *  - added -N16 option to put in delay between socket writes 16
 *  - increased MAX_SOCKET to 65535 since we were able to increase
 *	the number of file descripters with "ulimit -n 65535".
 *
 * Version 1.0.9 - Thurs 12 Feb 2009
 *  - added -b option to unbuffer output stream
 *  - added -f option to redirect output to file
 *
 * Version 1.0.8 - Friday 09 Jan 2009
 *  - added -N option to put in delay between socket writes.
 *
 * Version 1.0.7
 *  - added microsecond delay and -I option to debug timing, the -I
 *      adds additional delay since there is time required to obtain
 *      the debugging information.
 *
 * Version 1.0.6 - Friday 12 Dec 2008
 *  - use gettimeofday to measure write loop time and adjust.
 *
 * Version 1.0.5 - Monday 17 Nov 2008
 *  - Added pkts to Tx option (-c), moved Tx printf's to printStatLoop,
 *    changed regular printf's to use stdout, kept errors at stderr
 *
 * Version 1.0.4 - Monday 20 Oct 2008
 *  - Added server mode, reflect mode, client receive mode, debug mode,
 *	printStatLoop thread
 *
 * Version 1.0.3 - Friday 10 Oct 2008
 *  - Added ability to open multiple sockets
 *
 * Version 1.0.2 - Monday 22 Sep 2008
 *   - Added pkt_pattern function.
 *
 * Version 1.0.1 - Friday 27 June 2008
 *  - Initial release.
 */

#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <poll.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <sys/types.h>
#include <sys/errno.h>
#include <errno.h>
#include <sys/select.h>
#include <sys/time.h>
#include <pthread.h>
#include <signal.h>

#define MAX_SOCKETS 	65535
#define BUFF_SIZE	4096

static unsigned long writeCount = 0;
static unsigned long usDelay = 100;
static unsigned long usSockDelay = 0;
static int portNo = 0;
static int srcNo = 0;
static unsigned short msgLength = 128;
static struct sockaddr_in  dest;
static struct sockaddr_in  src;
static int sizeSockFD = 1;		/* default number of sockets = 1 */
static int userSockFD = 0;      	/* user can request up to MAX_SOCKETS */
static int SockDelayCount = 0;
static int numSockDelay = 1;      	/* user can request the number of sockets to insert Delay */
static int serverMode = 0;      	/* default is client mode */
static unsigned long pktsToTx = 0;      /* how many pkts client sends, 0 is forever */
static unsigned next_sent = 0;  	/* used in pkt_pattern */
static unsigned long rxCount = 0, txCount = 0; 	/* Total Rx and Tx packets */
static unsigned long rxBytes = 0, txBytes = 0; 	/* Rx and Tx Bytes, needed by printStatLoop */
static unsigned long rxPackets = 0, txPackets = 0;
static int readyFD = 0;		  	/* used by server, number of ready sockets to read */
static int debug = 0;			/* debugging mode */
static int sdebug = 0;  		/* show timing loops at start */
static int reflect = 0;			/* server will reflect traffic received */
static int clientRxMode = 0;		/* forks server in client mode */
static FILE *fptr = stdout;             /* File ptr for outputting to file */
static int unBuffer = 0;                /* option to unbuffer output */
static int useBusyWait = 0;     /* Method to generate short delays */
static int addRtpHeaders = 0;   /* Insert a simple incrementing RTP header */

static unsigned char cannedRtpHeader[12] = {
    0x80,  /* Version  and Flags */
    0x08,  /* M-bit flag, and Payload Type */
    0x00,  /* Sequence Number - byte 0 (gets updated) */
    0x00,  /* Sequence Number - byte 1 (gets updated) */
    0x12,  /* Timestamp - byte 0 (could be updated, but isn't here) */
    0x34,  /* Timestamp - byte 1 (could be updated, but isn't here) */
    0x56,  /* Timestamp - byte 2 (could be updated, but isn't here) */
    0x78,  /* Timestamp - byte 3 (could be updated, but isn't here) */
    0xa5,  /* SSRC Identifier - byte 0 */
    0x5a,  /* SSRC Identifier - byte 1 */
    0x3c,  /* SSRC Identifier - byte 2 */
    0xc3,  /* SSRC Identifier - byte 3 */
};
static unsigned short rtpSequenceNumber = 0;

void Usage(int exitCode);
void pkt_pattern(char *buf, int pkt_len);
void dumpbuff(char *buff, int len);
void goServer(int *fd);
void *printStatLoop( void *arg );
static void recv_sig(int signo);
inline unsigned long gethrtime();
inline int shorttime(u_int delay);

int main(int argc, char *argv[])
{
    unsigned long int start = 0, end = 0;
    static int firstloop=0;
    if (argc < 2)
        Usage(0);
    int destLen = sizeof(dest);
    memset(&dest, 0, destLen);
    int srcLen = sizeof(src);
    memset(&src, 0, srcLen);
    int fd_limit = -1;   /* set when fd limit is reached on system (usually FD_SETSIZE) */
    char destInfo[BUFF_SIZE];
    char srcInfo[BUFF_SIZE];

    int ch, ret=0;
    while ((ch = getopt(argc, argv, "bvxhrSDIti:o:p:s:w:d:l:n:N:m:c:f:R:")) != -1) {
    switch (ch) {
    default:
        fprintf(stderr, "getopt() returned %d (%c)\n", ch, ch);
        Usage(1); /* does not return */
    case 'v':
        fprintf(stdout, "%s: %s\n", argv[0], version);
        exit(0);
    case 'x':
        clientRxMode = 1;
        break;
    case 'h': Usage(0); /* does not return */
    case 'i':
        if (!inet_aton(optarg, &(dest.sin_addr))) {
            fprintf(stderr,
                "udpload: invalid IP address: \"%s\"\n", optarg);
            Usage(2);
        }
        break;
    case 'o':
        if (!inet_aton(optarg, &(src.sin_addr))) {
            fprintf(stderr,
                "udpload: invalid IP address: \"%s\"\n", optarg);
            Usage(2);
        }
        break;
    case 'p':
        portNo = strtoul(optarg, NULL, 0);
        break;
    case 's':
        srcNo = strtoul(optarg, NULL, 0);
        break;
    case 'w':
        writeCount = strtoul(optarg, NULL, 0);
        break;
    case 'd':
        usDelay = strtoul(optarg, NULL, 0);
        break;
    case 'l':
        msgLength = strtoul(optarg, NULL, 0);
        break;
    case 'n':
        userSockFD = strtoul(optarg, NULL, 0);
        break;
    case 'N':
        usSockDelay = strtoul(optarg, NULL, 0);
        break;
    case 'm':
        numSockDelay = strtoul(optarg, NULL, 0);
        break;
    case 'c':
        pktsToTx = strtoul(optarg, NULL, 0);
        break;
    case 'S':
        serverMode = 1;
        fprintf(stdout, "Server Mode on\n");
        break;
    case 'r':
        reflect = serverMode = 1;
        fprintf(stdout, "Reflect Mode on, implies Server Mode.\n");
        break;
    case 'D':
        debug = 1;
        break;
   case 'I':
        sdebug = 1;
        break;
    case 'f':
        if ( !( fptr = fopen(optarg, "w") ) ) {
            perror("udpload: opening outputfile");
            exit (1);
        }
        break;
    case 'b':
        unBuffer = 1;
        break;
    case 't':
        useBusyWait = 1;
        break;
    case 'R':
        addRtpHeaders = 1;
        rtpSequenceNumber = strtoul(optarg, NULL, 0) & 0xffff;
        fprintf(stderr, "Starting with RTP Seq Num = 0x%04x\n", rtpSequenceNumber);
        break;
    }
    }
    if (!serverMode) {
        if (portNo == 0) {
            fprintf(stderr,
                "udpload: must specify (non-zero) destination UDP port\n");
            Usage(2);
        }
        if (writeCount == 0) {
            fprintf(stderr,
                "udpload: must specify (non-zero) packets per loop\n");
            Usage(2);
        }
    }
    if (srcNo == 0) {  /* Required for now, eventhough syntax says no. */
        fprintf(stderr, "udpload: must specify (non-zero) source UDP port\n");
        Usage(2);
    }
    if (clientRxMode) {  /* reflect must be off, will manually fork server */
        serverMode = reflect = 0;
        fprintf(stdout, "Client Rx Mode on, turning off Server Mode and Reflect\n");
    }
    if (userSockFD > MAX_SOCKETS) {
        fprintf(stderr,
        "udpload: must specify less than %d sockets\n", MAX_SOCKETS);
        Usage(2);
    }
    else if (userSockFD > sizeSockFD) { sizeSockFD = userSockFD; }

    if (unBuffer) { /* unbuffer the fptr so there's no delay in I/O */
       	if ( setvbuf(fptr, NULL, _IONBF, 0) ) {
            perror("udpload: unbuffering FILE fptr stream");
            exit (1);
        }
        fprintf(stdout, "Unbuffering output stream.\n");
    }

    int sock_fd[sizeSockFD];    /* socket file descriptors array */
    for (int i=0; i<sizeSockFD; i++) { sock_fd[i] = 0; }

    int bound, conn;
    
    dest.sin_family = AF_INET;
    src.sin_family= AF_INET;
/*    if (serverMode)
	src.sin_addr.s_addr = htonl(INADDR_ANY);  */

    /* Creating sockets */
    for (int i=0; i<sizeSockFD; i++) {
        dest.sin_port = htons(portNo++);
        src.sin_port = htons(srcNo++);
        
        if ( (sock_fd[i] = socket(PF_INET, SOCK_DGRAM, IPPROTO_UDP)) < 0 ) {
            if ( errno == EMFILE ) { /* If max descriptors have been reached */
                perror("udpload: socket");
                fprintf(stderr, "Warning! Max open descriptors have been reached for your system at: %d\n", sock_fd[i-1]+1);
                fd_limit = i;
                break;
            }
            fprintf(stderr, "Got errno=%d\n", errno);
            perror("udpload: socket");
            return 3;
        }

        if ( (bound = bind(sock_fd[i], (struct sockaddr *) &src, sizeof(src))) < 0 ) {
            if ( errno == EADDRINUSE ) {   /* Skip over port number if address already in use */
                fprintf(stderr, "Warning! Got errno=%d: Skipping port number: %d\n", errno, portNo-1);
                fprintf(stderr, "Make sure the peer side knows about this!\n");
                perror("udpload: bind");
                /* Close this socket first before re-using file descriptor */
                if ( close(sock_fd[i--]) < 0 ) {
                    perror("udpload: close");
                }
                continue;
            }
            fprintf(stderr, "Got errno=%d\n", errno);
            perror("udpload: bind");
            return 3;
        }
    
    if (!serverMode) {
        if ( (conn = connect(sock_fd[i], (struct sockaddr *) &dest, sizeof(dest))) < 0 ) {
            perror("udpload: connect");
            return 3;
        }
    }

    } /* End creating sockets */

    if (fd_limit != -1)
        sizeSockFD = fd_limit;
    fprintf(stdout, "%d sockets created\n", sizeSockFD);
    
    if ( debug ) {
        socklen_t srcInfoLen = sizeof(srcInfo);
        for (int i=0; i<sizeSockFD; i++) {
            if ( getsockname(sock_fd[i], (struct sockaddr *) &src, &srcInfoLen) < 0 )
                perror("udpload: getsockname");
            fprintf(stdout, "sock_fd[%d] = %d, srcIP = %s, srcPort = %d\n", i, sock_fd[i],
                inet_ntop(AF_INET, &src.sin_addr, srcInfo, sizeof(srcInfo)), ntohs(src.sin_port));
        }
    }

    //unsigned long totalCount = 0;
    unsigned long loopCount = 0;
    int flags = 0;
/* This value isn't 12 (the size of the RTP header), because we also put
 * the RTP sequence number into the first two bytes AFTER the RTP header.
 * We also round this up for pkt_pattern()'s benefit.
 */
#define MINIMUM_UDP_PAYLOAD_FOR_RTP 16
    if (addRtpHeaders && (msgLength < MINIMUM_UDP_PAYLOAD_FOR_RTP))
        msgLength = MINIMUM_UDP_PAYLOAD_FOR_RTP;
    char *msg = new char[msgLength];

    /* Original memset - replaced with pkt_pattern()
    memset(msg,0xAA,msgLength);   */

    /* server mode - just run the server, and forget the rest */
    if ( serverMode ) {
        goServer(sock_fd);
    }
    
    pid_t childpid;

    /* clientRxMode - fork a process to run server, continue with client mode */
    if ( clientRxMode ) {
        if ( (childpid = fork()) == 0 ) {    /* child process */
            goServer(sock_fd);
            exit(0);
        }
        else if ( childpid < 0 ) {
            perror("udpload: clientRxMode server fork");
            return 4;
        }
        if ( debug )
            fprintf(stdout, "Got clientRxMode server child process id: %d\n", childpid);
    }

    /* Create a thread to print statistics */
    pthread_t tid;
    if ( pthread_create(&tid, NULL, printStatLoop, NULL) != 0 )
        perror("udpload: pthread_create");

    signal(SIGINT, recv_sig);  /* Catch interrupt signal and print approx total Tx */

    /* client mode - write loop */
    while ( (txCount < pktsToTx) || !pktsToTx ) {
        if (sdebug)
            start= gethrtime();
        for (loopCount = 0; loopCount < writeCount; loopCount++) {
            pkt_pattern(msg, msgLength);
            for (int i=0; i<sizeSockFD; i++) {
                if (send(sock_fd[i], msg, msgLength, flags) < 0) {
                    fprintf(stderr, "Problem calling send() ...\n");
                    perror("udpload: send");
                    return 4;
                }
                if ( debug ) {
                    socklen_t destInfoLen = sizeof(destInfo);
                    if ( getpeername(sock_fd[i], (struct sockaddr *) &dest, &destInfoLen) < 0 )
                        perror("udpload: getpeername");
                    fprintf(stdout, "Wrote %d bytes to %s on port %d\n", msgLength,
                            inet_ntop(AF_INET, &dest.sin_addr, destInfo, sizeof(destInfo)), ntohs(dest.sin_port));
                }
                txBytes += msgLength;
                txPackets++;
                txCount++;
                if (usSockDelay > 0) {
                    SockDelayCount++;
                    if (SockDelayCount >= numSockDelay) {
                        ret = shorttime(usSockDelay); //Delay between socket writes
                        SockDelayCount = 0;
                    }
                }
            }
        }
        if(sdebug) {
            end = gethrtime();    // time in usecs
        }
        ret = shorttime(usDelay); // Delay between messages
        if(sdebug) {
            if ( firstloop < 20 )
                printf("Print write loop time Start %lu, End %lu Diff %lu\n", start, end, (end - start) );
            start = gethrtime();    // time in usecs (time after delay loop)
            if (firstloop++ < 20 )
                printf("Delay through shorttime(), start %lu, end %lu, diff %lu\n", end, start, (start - end )); //Yes, swapped variables
        }
    } /* end client mode for-ever loop */

    fprintf(stdout, "\nFinished sending %lu packets.\n", txCount);

    if ( clientRxMode ) {
        if ( childpid > 0 ) {
            sleep(2);
            fprintf(stdout, "Killing child server process pid = %d.\n", childpid);
        if ( kill(childpid, SIGKILL) < 0 )
            perror("udpload: kill child process");
        }
    }

    for (int i=0; i<sizeSockFD; i++) {
        if ( close(sock_fd[i]) < 0 )
            perror("udpload: close");
    }
    fprintf(stdout,"\nClosed %d sockets.\nDone.\n", sizeSockFD);

    return 0;
}

void goServer(int *sock_fd)
{
    struct sockaddr_in cliaddr;
    char clientInfo[BUFF_SIZE];
    char *rxBuff = new char[BUFF_SIZE];
    int flags = 0;
    int rxLen = 0;
    int maxfdp1;                /* used with 'select' (highest descriptor num + 1) */
    fd_set rset, rset_orig;     /* used with 'select' (receive descriptor set) */
    int lastReceivedIndex = -1;
    int j=0;                    /* index num in for-ever loop */
    socklen_t len;
    
    memset(&cliaddr, 0, sizeof(cliaddr));
    memset(clientInfo, 0, BUFF_SIZE);
    memset(rxBuff, 0, BUFF_SIZE);
    
    /*** Try increasing Rx and Tx Buffers ***/
   /*int n, setn;
    *socklen_t nLen;
    *nLen = sizeof(n);
    *
    *getsockopt(sock_fd[0], SOL_SOCKET, SO_RCVBUF, &n, &nLen);
    *printf("default: SO_RCVBUF = %d\n", n);
    *getsockopt(sock_fd[0], SOL_SOCKET, SO_SNDBUF, &n, &nLen);
    *printf("default: SO_SNDBUF = %d\n", n);
    *
    *setn = 220 * 1024;
    *for (int i=0; i<sizeSockFD; i++) {
    *   setsockopt(sock_fd[i], SOL_SOCKET, SO_RCVBUF, &setn, sizeof(setn));
    * 	printf("Setting SO_RCVBUF to %d\n", setn);
    * 	getsockopt(sock_fd[i], SOL_SOCKET, SO_RCVBUF, &n, &nLen);
    * 	printf("after changing, SO_RCVBUF = %d\n", n);
    *}
    ***************************************/
    
    FD_ZERO(&rset_orig); /* clear all bits in descriptor set */
    printf("FD_SETSIZE = %d\n", FD_SETSIZE);

    for (int i=0; i<sizeSockFD; i++)
        FD_SET(sock_fd[i], &rset_orig); /* turn on bits to check for rset */

    /* Create a thread to print receive statistics */
    pthread_t tid;
    if ( pthread_create(&tid, NULL, printStatLoop, NULL) != 0 )
    perror("udpload: pthread_create");

    /* tell select which range of bits to check */
    maxfdp1 = sock_fd[sizeSockFD-1] + 1;

    /* Continue with Server Mode */
    for (;;) { /* forever */

        rset = rset_orig;   /* refresh rset */

        /* block until there are socket(s) ready */
        if ( (readyFD = select(maxfdp1, &rset, NULL, NULL, NULL)) < 0 ) {
            perror("udpload: select");
            exit(5);
        }
        if ( debug )
            fprintf(stdout, "readyFD = %d\n", readyFD);

        j = lastReceivedIndex;

        /* Fair Round Robin Receive */
        do {
            if ( ++j >= sizeSockFD )
                j=0;
            if (FD_ISSET(sock_fd[j], &rset)) { /* socket is readable */
                len = sizeof(cliaddr);
                if ( (rxLen = recvfrom(sock_fd[j], rxBuff, BUFF_SIZE, flags,
                        (struct sockaddr *) &cliaddr, &len)) < 0 ) {
                    perror("udpload: recvfrom");
                    exit(5);
                }
                if ( reflect ) {  /* Reflect traffic received back at the sender */
                    if ( sendto(sock_fd[j], rxBuff, rxLen, flags, (const struct sockaddr *) &cliaddr, len) < 0 ) {
                        perror("udpload: sendto");
                        exit(5);
                    }
                }
                if ( debug ) {
                    fprintf(stdout, "Received %d bytes from %s on port %d\n", rxLen,
                    	inet_ntop(AF_INET, &cliaddr.sin_addr, clientInfo, sizeof(clientInfo)), ntohs(cliaddr.sin_port));
                    dumpbuff(rxBuff, rxLen);
                    if ( reflect ) {
                        fprintf(stdout, "Reflected %d bytes to %s on port %d\n", rxLen,
                            inet_ntop(AF_INET, &cliaddr.sin_addr, clientInfo, sizeof(clientInfo)), ntohs(cliaddr.sin_port));
                    }
                }
                rxBytes += rxLen;
                rxPackets++;
                rxCount++;
                lastReceivedIndex = j;
            }
        } while ( j != lastReceivedIndex );

    } /* end for (;;) */
    for (int i=0; i<sizeSockFD; i++) {  /* Not expected to run, but good practice */
        if ( close(sock_fd[i]) < 0 )
            perror("udpload: close");
    }

}

void Usage(int exitCode)
{
    fprintf(stderr, "\nudpload - send a wheelbarrow full of UDP packets\n\n");
	fprintf(stderr, "    %s\n", version);
    fprintf(stderr, "Usage:\n  udpload -i <remote IP address> (client only)\n");
    fprintf(stderr, "          -p <remote UDP port> (client only)\n");
    fprintf(stderr, "          -w <packets per loop> (client only)\n");
    fprintf(stderr, "          -o <local IP address>\n");
    fprintf(stderr, "          -s <local UDP port>\n");
    fprintf(stderr, "        [ -d <microsecond delay per loop (default 100us)> ] (client only)\n");
    fprintf(stderr, "        [ -l <packet length (default 128 bytes)> ] (client only)\n");
    fprintf(stderr, "        [ -c <packets to Tx (must be multiple of (-w * -n), default is forever)>\n");
    fprintf(stderr, "        [ -n <number of sockets (default 1)> ]\n");
    fprintf(stderr, "               In client mode: writes to 'n' sockets.\n");
    fprintf(stderr, "               In server mode: receives from 'n' sockets.\n");
    fprintf(stderr, "        [ -N <microsecond delay between socket writes (default 0us)> ] (client)\n");
    fprintf(stderr, "        [ -m <number of sockets to delay between (default every 1 socket)> ]\n");
    fprintf(stderr, "        [ -x ] Forks a server process in client mode to receive packets.\n");
    fprintf(stderr, "               Ignores -S option, and turns off reflect.\n");
    fprintf(stderr, "        [ -S ] Run in server mode (default client mode).\n");
    fprintf(stderr, "               Ignores -i and -p options, and any write options (d,w,l).\n");
    fprintf(stderr, "        [ -r ] Reflect packets back at sender.  Implies server mode.\n");
    fprintf(stderr, "        [ -D ] Debug mode, verbose output.\n");
    fprintf(stderr, "        [ -v ] Show version and quit.\n");
    fprintf(stderr, "        [ -I ] Show timing of first twenty loops.\n");
    fprintf(stderr, "        [ -b ] Unbuffer the output stream so there's no delay in I/O.\n");
    fprintf(stderr, "        [ -f <outputfile> ] Redirect printStatLoop thread output to <outputfile>\n");
    fprintf(stderr, "        [ -t ] Use busy-wait timing (100%% CPU usage, but more accurate)\n");
    fprintf(stderr, "        [ -R <initial_seq_num> ] Insert sequential RTP headers (client only)\n");
    exit(exitCode);
}

void pkt_pattern(char *buf, int pkt_len)
{
    int z;
    int start = 0;
    unsigned int *pi, tmp;
    unsigned short netSeqNum;

    if (addRtpHeaders) {
        memcpy(buf, cannedRtpHeader, sizeof(cannedRtpHeader));
        netSeqNum = htons(rtpSequenceNumber);
        rtpSequenceNumber++;
        ((unsigned short *) buf)[1] = netSeqNum; /* The real RTP sequence number */
        ((unsigned short *) buf)[6] = netSeqNum; /* Copy remains after stripping RTP */
        start = 16; /* Adjust the starting point for the rest of the pattern */
    }

    pi = (unsigned int *) &(buf[start]);
    for (z = start/4; z < pkt_len/4; z++)
    {
        tmp = ((z << 24) | next_sent);
        tmp = htonl(tmp);
        *pi++ = tmp;
    }
    next_sent++;
    return;
}

void dumpbuff(char *pc, int len) { /* show it */
    int i;

    printf("Dumping block size %d:\n", len);
    for(i = 0; i < len;)
    {
        if (!(i % 16))
            printf("%04x: ", i);
        if (!(i % 4))
            printf(" ");
        printf("%02x ", *pc++);
        if (!(++i % 16))
            printf("\n");
    }
    printf("\n");
}

void *printStatLoop( void *arg ) {
    int delay = 1000;

    if ( debug )
        delay = 1;
    int rxStart = 0, txStart = 0;
    int spd = 0;
    float throughput = 0; 
    char bps[3][5] = {"bps","Kbps","Mbps"};
    
    fprintf(fptr,"printStatLoop thread started.\n");
    
    for ( ; ; ) {
        if ( (txBytes > 0) || txStart ) {  /* Print Tx Info */
            throughput = txBytes * 8;
            if ( throughput > 1000000 ) {
                throughput /= 1000000;
                spd=2;
            }
            else if ( throughput > 1000 ) {
                throughput /= 1000;
                spd=1;
            }
            fprintf(fptr, "Transmitted %lu bytes/sec, %.2f %s, %lu packets/sec, %lu packets total.\n",
                    txBytes, throughput, bps[spd], txPackets, txCount);
            if ( !txBytes )
                txStart--;    /* print stats 2 more times after transmitting 0 pkts */
            else
                txStart = 2;
            txBytes = txPackets = spd = 0;
        }
        if ( (rxBytes > 0) || rxStart ) {  /* Print Rx Info */
            throughput = rxBytes * 8;
            if ( throughput > 1000000 ) {
                throughput /= 1000000;
                spd=2;
            }
            else if ( throughput > 1000 ) {
                throughput /= 1000;
                spd=1;
            }
            fprintf(fptr, "Received %lu bytes/sec, %.2f %s, %lu packets/sec, %lu packets total.\n",
                    rxBytes, throughput, bps[spd], rxPackets, rxCount);
            if ( reflect )
                fprintf(fptr, "Reflected %lu bytes/sec, %.2f %s, %lu packets/sec, %lu packets total.\n",
                        rxBytes, throughput, bps[spd], rxPackets, rxCount);
            if ( !rxBytes )
                rxStart--;    /* print stats 2 more times after receiving 0 pkts */
            else
                rxStart = 2;
            rxBytes = rxPackets = spd = 0;
        }
        poll(NULL, 0, delay);
    }
    return (NULL);
}

static void recv_sig(int signo) {
    if (!serverMode)
        fprintf(stdout,"\n Interrupt signal caught, signo=%d.  Total transmitted packets is ~ %lu\n", signo, txCount);
    exit(0);
}

inline unsigned long gethrtime()
{
    unsigned long k;
    int ret, i;
    struct timeval gt;

    for ( i=0; i<100; i++ ) {
        ret = gettimeofday(&gt, NULL);
        if ( ret >= 0 )
            break;
    }
    if( i >= 100 ) {
        printf("udpload: gettimeofday() returned -1, quitting thread.\n");
        exit(1);
    }
    k = gt.tv_sec * 1000000L + gt.tv_usec;
    return( k );
}

inline int shorttime(u_int delay)
{
    if (useBusyWait) {
        static const unsigned long fudge = 3LU;
        unsigned long int k, initial;
        int ret;
        struct timeval gt;
        ret = gettimeofday(&gt,NULL);
        if ( ret < 0 )
            return(ret);
        initial = gt.tv_sec * 1000000L + gt.tv_usec;
        do  {
            ret = gettimeofday(&gt,NULL);
            if (ret < 0)
                break;
            k = gt.tv_sec * 1000000L + gt.tv_usec;
        } while ( ( k - initial + fudge ) < (unsigned long)delay);
        return( ret );
    }
    else {
        struct timespec requested_t, remaining_t;

        requested_t.tv_sec = 0;
        requested_t.tv_nsec = delay;
        for (;;) {
            if (!nanosleep(&requested_t, &remaining_t))
                return 0;
            if (errno != EINTR)
                return -1;
            memcpy(&requested_t, &remaining_t, sizeof(struct timespec));
        }
    }
}
