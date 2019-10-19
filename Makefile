PROG= svnup
SRCS= svnup.c

LDADD= -lssl -lmd

WARNS= 6

MAN= svnup.1 svnup.conf.5

.include <bsd.prog.mk>

