
#define sizeofel(e) (sizeof(e)/sizeof(*e))

typedef long LONG;
typedef char CHAR;
typedef unsigned char UCHAR;

typedef struct _REPORT_RATE {
    CHAR Command;
    UCHAR ReportRate;
} REPORT_RATE;

/* static */ REPORT_RATE ReportRateTable[] = {
        {'D', 0 },
        {'J', 10},
        {'K', 20},
        {'L', 35},
        {'R', 50},
        {'M', 70},
        {'Q', 100},
        {'N', 150},
        {'O', 151}      // Continuous
};

int main(void)
{
  LONG count;

  for (count = sizeofel(ReportRateTable) - 1; count >= 0; count--) {
      ;
  }

  return 0;
}
