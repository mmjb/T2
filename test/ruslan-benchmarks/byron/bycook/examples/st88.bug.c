// Property: F G WItemsNum >= 1

int WItemsNum;

 inline void init() { WItemsNum = nondet(); }

 inline void callback1() {}
 inline void callback2() {}
#define MoreWItems() nondet()

inline void body() {
    WItemsNum = nondet();
    while(1) {
        while(WItemsNum<=5 && MoreWItems()) {
               if (WItemsNum<=5) {
                   callback1();
                   WItemsNum++;
    
               } else {
                   WItemsNum++;
               }
        }
    
        while(WItemsNum>2) {
             callback2();
             WItemsNum--;
        }
    }
    while(1) {}
}
    
 int main() { init(); body(); }
