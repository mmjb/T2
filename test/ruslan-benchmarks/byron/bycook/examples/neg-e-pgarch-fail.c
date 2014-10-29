// #include "ctl.h"

// Property: G F wakened==1

int wakend;
unsigned int pc;
 inline int __phi() { return CEF(CAG(CAP(wakend != 1))); }

/*
 * pgarch_MainLoop
 *
 * Main loop for archiver
 */
int          last_copy_time = 0;
int          curtime;
#define true 1
#define false 0
#define NULL 0
#define PGC_SIGHUP 1
int got_SIGHUP;

int __rho_1_;
int __rho_2_;
int __rho_3_;
int __rho_4_;
int __rho_5_;
int __rho_6_;
int __rho_7_;

 inline void init() {
  wakend = 1; __rho_1_ = nondet(); got_SIGHUP = __rho_2_;
}


 inline void ProcessConfigFile(int a) {}
#define XLogArchivingActive() nondet()
 inline void pgarch_ArchiverCopyLoop() { }
#define time(a) nondet()
 inline void pg_usleep(int a) {}
#define PGARCH_AUTOWAKE_INTERVAL 1000
#define PostmasterIsAlive(a) nondet()

inline void body() {

        /*
         * We run the copy loop immediately upon entry, in case there are
         * unarchived files left over from a previous database run (or maybe
         * the archiver died unexpectedly).  After that we wait for a signal
         * or timeout before doing more.
         */
        wakend = true;

        while(1)
        {
                /* Check for config update */
                if (got_SIGHUP>0)
                {
                        got_SIGHUP = 0;
                        ProcessConfigFile(PGC_SIGHUP);
			__rho_5_ = XLogArchivingActive();
			int tt = __rho_5_;
			  if (tt<=0)
                                break;                  /* user wants us to shut down */
                }
                /* Do what we're here for */
                if (wakend>0)
                {
                        wakend = 0;
                        pgarch_ArchiverCopyLoop();
			__rho_6_ = time(NULL);
                        last_copy_time = __rho_6_;
                }
                /*
                 * There shouldn't be anything for the archiver to do except to
                 * wait for a signal, ... however, the archiver exists to
                 * protect our data, so she wakes up occasionally to allow
                 * herself to be proactive. In particular this avoids getting
                 * stuck if a signal arrives just before we sleep.
                 */
                if (wakend<=0)
                {
		  //pg_usleep(PGARCH_AUTOWAKE_INTERVAL * 1000000L);

                        __rho_7_ = time(NULL);
			curtime = __rho_7_;
                        if ((curtime - last_copy_time) >=
			     PGARCH_AUTOWAKE_INTERVAL)
                                wakend = true;
                }
		__rho_4_ = nondet();
		dummy = __rho_4_; //  PostmasterIsAlive(true);
		if (dummy<=0) break;
        }

  while(1) { dummy=dummy; } L_return: return 0;
}

 int main() { init(); body(); }
