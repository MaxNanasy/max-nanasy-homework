#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <dirent.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <pwd.h>
#include <grp.h>
#include <time.h>
#include <limits.h>

#define OPTSTRING ("aAL")

struct options { bool all, almostAll, dereference, oneArgument ; } ;
struct pathAndStat { char *path; struct stat stats ; } ;

static struct options options;
static int cwdFD;

void perror2 (char *string0, char *string1)
{
  fprintf (stderr, "%s: ", string0);
  perror (string1);
}

struct options getOptions (int argc, char **argv)
{

  struct options options = { false, false, false, false } ;
  int option;

  do {
    switch (option = getopt (argc, argv, OPTSTRING)) {
    case 'a': options.all         = true; break;
    case 'A': options.almostAll   = true; break;
    case 'L': options.dereference = true; break;
    case -1 :                             break;
    default : exit (EXIT_FAILURE);
    }
  } while (option != -1);

  options.oneArgument = optind >= argc - 1 ;

  return options;

}

int compareFileSizes (struct pathAndStat *file0, struct pathAndStat *file1)
{
  return file1 -> stats . st_size - file0 -> stats . st_size ;
}

int mlstat (const char *path, struct stat *buf)
{
  return options.dereference ? stat (path, buf) : lstat (path, buf);
}

char typeChar (mode_t st_mode)
{
  if      (S_ISREG  (st_mode))
    return '-';
  else if (S_ISDIR  (st_mode))
    return 'd';
  else if (S_ISCHR  (st_mode))
    return 'c';
  else if (S_ISBLK  (st_mode))
    return 'b';
  else if (S_ISFIFO (st_mode))
    return 'p';
  else if (S_ISLNK  (st_mode))
    return 'l';
  else if (S_ISSOCK (st_mode))
    return 's';
  else
    return '?';
}

void permissionString (mode_t permissions, bool sid, bool sticky, char *pString)
{
  pString [0] = permissions & S_IROTH ? 'r' : '-' ;
  pString [1] = permissions & S_IWOTH ? 'w' : '-' ;
  pString [2] = permissions & S_IXOTH ? sid ? 's' : sticky ? 't' : 'x' : sid ? 'S' : sticky ? 'T' : '-' ;
}

void modeString (mode_t st_mode, char *mString)
{
  mString [0] = typeChar (st_mode);
  permissionString ((st_mode & S_IRWXU) >> 6, st_mode & S_ISUID, false            , mString + 1);
  permissionString ((st_mode & S_IRWXG) >> 3, st_mode & S_ISGID, false            , mString + 4);
  permissionString ( st_mode & S_IRWXO      , false            , st_mode & S_ISVTX, mString + 7);
}

void timeStampString (time_t timeStamp, char *tsString)
{
  strftime (tsString, 20, "%Y-%m-%d %H:%M", localtime (&timeStamp));
}

void processDerivedFile (struct pathAndStat file)
{
  char mString [11], tsString [20], link [PATH_MAX + 1];
  struct passwd *userPasswd ;
  struct group  *groupPasswd;
  int n;
  modeString (file . stats . st_mode, mString);
  mString [10] = '\0' ;
  userPasswd  = getpwuid (file . stats . st_uid);
  groupPasswd = getgrgid (file . stats . st_gid);
  timeStampString (file . stats . st_mtime, tsString);
  printf ("%s %3d %-8s %-8s %7d %s %s", mString, (int) file . stats . st_nlink, userPasswd -> pw_name, groupPasswd -> gr_name, (int) file . stats . st_size, tsString, file . path);
  if (S_ISLNK (file . stats . st_mode) && ! options.dereference) {
    n = readlink (file . path, link, PATH_MAX);
    link [n] = '\0';
    printf (" -> %s", link);
  }
  putchar ('\n');
}

int almostAllFileName (const struct dirent *directoryEntry)
{
  return ! (directoryEntry -> d_name [0] == '.' && (directoryEntry -> d_name [1] == '\0' || (directoryEntry -> d_name [1] == '.' && directoryEntry -> d_name [2] == '\0'))) ;
}

int nonHiddenFileName (const struct dirent *directoryEntry)
{
  return directoryEntry -> d_name [0] != '.' ;
}

void processDirectoryFiles (struct dirent **namelist, int numberOfEntries)
{
  struct pathAndStat files [numberOfEntries];
  int i;
  for (i = 0; i < numberOfEntries; ++ i) {
    files [i] . path = namelist [i] -> d_name ;
    mlstat (namelist [i] -> d_name, & files [i] . stats);
  }
  qsort (files, numberOfEntries, sizeof (struct pathAndStat), (int (*) (const void *, const void *)) compareFileSizes);
  for (i = 0; i < numberOfEntries; ++ i)
    processDerivedFile (files [i]);
}

void processDirectory (char *path)
{
  struct dirent **namelist;
  int numberOfEntries, i;
  numberOfEntries = scandir (path, &namelist, options.all ? 0 : options.almostAll ? almostAllFileName : nonHiddenFileName , alphasort);
  if (chdir (path) < -1)
    perror2 ("chdir", path);
  else {
    processDirectoryFiles (namelist, numberOfEntries);
    fchdir (cwdFD);
  }
  for (i = 0; i < numberOfEntries; ++ i)
    free (namelist [i]);
  free (namelist);
}

void processExplicitPath (char *path)
{
  struct stat stats;
  struct pathAndStat file;

  if (mlstat (path, &stats) < 0)
    perror2 ("stat", path);
  else if (S_ISDIR (stats.st_mode)) {
    if (! options.oneArgument)
      printf ("%s:\n", path);
    processDirectory (path);
  }
  else {
    file . path  = path  ;
    file . stats = stats ;
    processDerivedFile (file);
  }
}

int main (int argc, char *argv [])
{

  options = getOptions (argc, argv);
  int i;

  cwdFD = open (".", 0);

  if (optind == argc)
    processExplicitPath (".");
  else
    for (i = optind; i < argc; ++ i)
      processExplicitPath (argv [i]);

  return EXIT_SUCCESS;

}
