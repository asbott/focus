
#include "test2.h"

#define MACRO1

#define MACRO2

#define MACRO3(...)

// unions
// #defines
// enum members

typedef struct Struct1 {
	int member1;
} Struct2;

struct {
	NoType anon1;
	Struct1 anon2;
};
NotAStruct

typedef union Union1 {
	int member1;
} Union2;

union {
	NoType2 anon1;
	Union1 anon2;
}

enum {
	ANON1,
	ANON2,
	ANON3,
}
NotAType

typedef enum Enum1 {
	MEMBER11,
	MEMBER22,

	MEMBER33
} Enum1;

typedef enum  {
	MEMBER1,
	MEMBER2,

	MEMBER3
} Enum2;
NOTYPE

typedef struct Struct7 {
	NoType m;
	int member1;
} Struct7;

// Should be types
Enum1
Enum2
Struct2
Union1
Union2
Union3
Struct3;
Struct4
Struct5
Struct6
Struct7
Struct // regular identifier

// Should be regular identifier
Undeclared
Undeclared2
NoType
NoType2
Nothing
NotAType
NotAStruct
NOTYPE // regular identifier

// Should be enum constants
ANON1
ANON2
ANON3
MEMBER1
MEMBER2
MEMBER3
MEMBER11
MEMBER22
MEMBER33
MEMBER111
MEMBER222
MEMBER333
MEMBER // regular identifier

// should be macros
MACRO1
MACRO2
MACRO3
MACRO // regular identifier