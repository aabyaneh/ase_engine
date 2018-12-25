/*
  dirname - return directory part of PATH.

  source code:
  glibc-2.28/misc/dirname.c
  glibc-2.28/string/
  https://github.com/lattera/glibc/blob/895ef79e04a953cac1493863bcae29ad85657ee1/misc/dirname.c
  https://github.com/lattera/glibc/blob/895ef79e04a953cac1493863bcae29ad85657ee1/string/strrchr.c
  https://opensource.apple.com/source/BerkeleyDB/BerkeleyDB-18/db/clib/strchr.c.auto.html

  help:  http://www.gnu.org/software/libc/manual/html_mono/libc.html
*/

uint64_t* dot;

// find the first occurrence of c in s
uint64_t* strchr(uint64_t* s, uint64_t c) {
  while (1) {
    if (*s == c)
      return s;
    if (*s == 0)
      return (uint64_t*) 0;

    s = s + 1;
  }
}

// find the last occurrence of c in s
uint64_t* strrchr(uint64_t* s, uint64_t c) {
  uint64_t* found;
  uint64_t* p;

  if (c == 0)
    return strchr(s, 0);

  found = (uint64_t*) 0;
  p = strchr(s, c);
  while (p != (uint64_t*) 0) {
    found = p;
    s = p + 1;
    p = strchr(s, c);
  }

  return found;
}

uint64_t* dirname(uint64_t* path) {
  uint64_t* last_slash;
  uint64_t* runp;
  uint64_t  loop;

  dot = (uint64_t*) ".";

  /* Find last '/'.  */
  if (path != (uint64_t*) 0)
    last_slash = strrchr(path, '/');
  else
    last_slash = (uint64_t*) 0;

  if (last_slash != (uint64_t*) 0) {
    if (last_slash != path) {
      if (*(last_slash + 1) == 0) {

        // Determine whether all remaining characters are slashes.
        runp = last_slash;
        loop = 1;
        while (loop) {
          if (runp != path) {
            if (*(runp - 1) != '/')
              loop = 0;
            else
              runp = runp - 1;
          } else
            loop = 0;
        }

        /* The '/' is the last character, we have to look further.  */
        loop = 1;
        while (loop) {
          if (runp != path) {
            runp = runp - 1;
            if (*runp == '/') {
              last_slash = runp;
              loop = 0;
            }
          } else {
            last_slash = (uint64_t*) 0;
            loop = 0;
          }
        }

      }
    }
  }

  if (last_slash != (uint64_t*) 0) {
    // Determine whether all remaining characters are slashes.
    runp = last_slash;
    loop = 1;
    while (loop) {
      if (runp != path) {
        if (*(runp - 1) != '/')
          loop = 0;
        else
          runp = runp - 1;
      } else
        loop = 0;
    }

    if (runp == path) {
      if (last_slash == path + 1)
  	    last_slash = last_slash + 1;
  	  else
  	    last_slash = path + 1;
    } else
      last_slash = runp;

    *last_slash = 0;

  } else
    path = dot;

  return path;
}

uint64_t main() {
  uint64_t* str;
  uint64_t* ptr;

  /*
  symbolic code:
    - input: an array of symbolic characters with a fixed length.
      - in fact the length of input string can be symbolic as each symbolic character
        interval can contain 0 (which means end of string)
  */

  /* code */
  str = malloc(6 * 8);
  *(str + 0) = '/';
  *(str + 1) = 'x';
  *(str + 2) = 'y';
  *(str + 3) = '/';
  *(str + 4) = 'r';
  *(str + 5) = 0;

  ptr = dirname(str);

  return 0;
}