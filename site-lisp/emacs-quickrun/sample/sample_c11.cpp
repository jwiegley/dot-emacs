#include <iostream>
#include <vector>
#include <string>

/*
(quickrun-add-command "c++/c11"
                      '((:command . "g++")
                        (:exec    . ("%c -std=c++0x %o -o %n %s"
                                     "%n %a"))
                        (:remove  . ("%n")))
                      :default "c++")
*/

int main ()
{
    std::vector <std::string> lst = { "a", "b", "c", "d" };

    for (auto x : lst){
        std::cout << "[" << x << "]" << std::endl;
    }

    return 0;
}
