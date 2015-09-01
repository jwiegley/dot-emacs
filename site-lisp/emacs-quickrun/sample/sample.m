#ifdef __APPLE__
#import <stdio.h>
#import <Foundation/NSObject.h>
#else
#import <stdio.h>
#import <objc/Object.h>
#endif

#ifdef __APPLE__
@interface HelloClass : NSObject
#else
@interface HelloClass : Object
#endif
- (void)helloWorld;
@end

@implementation HelloClass
- (void)helloWorld {
    printf("Hello world!\n");
}
@end

int main() {
    id obj = [HelloClass alloc];
    [obj helloWorld];
    return 0;
}
