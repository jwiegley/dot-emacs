// $Id: aclass.h,v 1.3 2005/04/01 06:05:06 ryants Exp $
// This is just some silly sample file to test out doxymacs with.
#ifndef _ACLASS_H_
#define _ACLASS_H_


#define SOME_OBSCURE_DEFINE	76

/**
 * This class does blah.
 *
 */
class Foo
{
  public:
    /**
     * The constructor.
     *
     * @param blah	Some kind of fish.
     */
    Foo(int blah)
        : _blah(blah)
        {}

    /**
     * Gets the current value of blah.
     */
    GetBlah(void) const { return _blah; }

    enum blah_blah
        {
            BAZ,
            BAZ2,
        };

  private:

    /**
     * Testing the in/out parameter stuff.
     *
     * @param[in] in An "in" parameter
     * @param[out] out An "out" parameter
     * @param[in,out] inout An "inout" parameter
     */
    Foo(int &in, int &out, int &inout) { out = in + inout; }

    /** This is a measure of our blahness. */
    int _blah;
};

/** This struct does something useless */
struct blah
{
    int x;
    int y;
};

typedef struct
{
    int z;
} baz;

/** This is a useless enum */
enum _blah
{
    FOO_SNAZ,                   /**< More silly stuff. */
    Foo
};

/** Some namespace */
namespace NameSpaceTest
{
    int foobazbar;
}

#endif // _ACLASS_H_
