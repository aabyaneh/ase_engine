/*
  Function: int fnmatch (const char *pattern, const char *string, int flags)

  This function tests whether the string string matches the pattern pattern. It returns 0 if they do match; otherwise, it returns the nonzero value FNM_NOMATCH. The arguments pattern and string are both strings.

  flags are not implemented. assume flags = 0

  source code: http://web.mit.edu/freebsd/csup/fnmatch.c
  help:        http://www.gnu.org/software/libc/manual/html_mono/libc.html#Wildcard-Matching
*/

// uint64_t FNM_NOESCAPE    = 0x01;	/* Disable backslash escaping. */
// uint64_t FNM_PATHNAME    = 0x02;	/* Slash must be matched by slash. */
// uint64_t FNM_PERIOD      = 0x04;	/* Period must be matched by period. */
// uint64_t FNM_LEADING_DIR = 0x08;	/* Ignore /<tail> after Imatch. */
// uint64_t FNM_CASEFOLD    = 0x10;	/* Case insensitive search. */
// uint64_t FNM_PREFIX_DIRS = 0x20;	/* Directory prefixes of pattern match too. */

uint64_t FNM_NOMATCH =	1;	// Match failed.
uint64_t EOS = 0;           // End of String

uint64_t CHAR_BACKSLASH = 92;

uint64_t* rangematch(uint64_t* pattern, uint64_t test, uint64_t flags);

uint64_t fnmatch(uint64_t* pattern, uint64_t* string, uint64_t flags) {
	uint64_t* stringstart;
	uint64_t c;
  uint64_t test;

  while (1) {
    c = *pattern;
    pattern = pattern + 1;
    if (c == EOS) {
      if (*string == EOS) {
        return 0;
      } else {
        return FNM_NOMATCH;
      }
      /* case 'EOS' */

    } else if (c == '?') {
      if (*string == EOS) {
				return FNM_NOMATCH;
      }
			string = string + 1;
      /* case '?' */

    } else if (c == '*') {
      c = *pattern;

			/* Collapse multiple stars. */
			while (c == '*') {
        pattern = pattern + 1;
				c = *pattern;
      }

			/* Optimize for pattern with * at end or before /. */
			if (c == EOS) {
				return 0;
      }

      /* General case, use recursion. */
      test = *string;
      while (test != EOS) {
        if (fnmatch(pattern, string, 0) == 0) {
          return 0;
        }

        string = string + 1;
        test = *string;
      }

      return FNM_NOMATCH;
      /* case '*' */

    } else if (c == '[') {
      if (*string == EOS) {
				return FNM_NOMATCH;
      }
      pattern = rangematch(pattern, *string, 0);
			if (pattern == (uint64_t*) 0) {
				return FNM_NOMATCH;
      }
			string = string + 1;
      /* case '[' */

    } else if (c == CHAR_BACKSLASH) {
      c = *pattern;
      pattern = pattern + 1;
			if (c == EOS) {
				c = CHAR_BACKSLASH;
				pattern = pattern -  1;
			}

      // FALLTHROUGH
      if (c != *string) {
        return FNM_NOMATCH;
      }
			string = string + 1;
      // case

    } else {
      // default case
      if (c != *string) {
        return FNM_NOMATCH;
      }
			string = string + 1;
		}

  } // while
  // not reachable
}

uint64_t* rangematch(uint64_t* pattern, uint64_t test, uint64_t flags) {
	uint64_t negate;
  uint64_t ok;
	uint64_t c;
  uint64_t c2;

  if (*pattern == '!') {
    negate = 1;
  } else if (*pattern == '^') {
    negate = 1;
  } else {
    negate = 0;
  }

	if (negate) {
		pattern = pattern + 1;
  }

  ok = 0;
  c = *pattern;
  pattern = pattern + 1;
  while (c != ']') {
    if (c == CHAR_BACKSLASH) {
		  c = *pattern;
      pattern = pattern + 1;
    }

		if (c == EOS) {
			return (uint64_t*) 0;
    }

    if (*pattern == '-') {
      c2 = *(pattern+1);
      if (c2 != EOS) {
        if (c2 != ']') {
          pattern = pattern + 2;
    			if (c2 == CHAR_BACKSLASH) {
            c2 = *pattern;
            pattern = pattern + 1;
          }

    			if (c2 == EOS) {
    				return (uint64_t*) 0;
          }

    			if (c <= test) {
            if (test <= c2) {
              ok = 1;
            }
          }
        }
      }
    } else if (c == test) {
			ok = 1;
    }

    c = *pattern;
    pattern = pattern + 1;
  }

  if (ok == negate) {
    return (uint64_t*) 0;
  } else {
    return pattern;
  }
}

uint64_t main() {
  uint64_t* pattern_str;
  uint64_t* str;
  uint64_t  res;

  /*
  symbolic code:
    - this benchmark is nice for checking whether a symbolic char is whitin a range (e.g. [0-9])
    - input:
      - fixed pattern.
      - symbolic string array of fixed length.
      - flags = 0.
  */

  // pattern: ".?[a-z0-9]*?*[a-z0-9]"
  pattern_str = malloc(22 * 8);
  *(pattern_str + 0) = '.';
  *(pattern_str + 1) = '?';
  *(pattern_str + 2) = '[';
  *(pattern_str + 3) = 'a';
  *(pattern_str + 4) = '-';
  *(pattern_str + 5) = 'z';
  *(pattern_str + 6) = '0';
  *(pattern_str + 7) = '-';
  *(pattern_str + 8) = '9';
  *(pattern_str + 9) = ']';
  *(pattern_str + 10) = '*';
  *(pattern_str + 11) = '?';
  *(pattern_str + 12) = '*';
  *(pattern_str + 13) = '[';
  *(pattern_str + 14) = 'a';
  *(pattern_str + 15) = '-';
  *(pattern_str + 16) = 'z';
  *(pattern_str + 17) = '0';
  *(pattern_str + 18) = '-';
  *(pattern_str + 19) = '9';
  *(pattern_str + 20) = ']';
  *(pattern_str + 21) = 0;

  // string: ".XaXa"
  str = malloc(6 * 8);
  *(str + 0) = '.';
  *(str + 1) = 'X';
  *(str + 2) = 'a';
  *(str + 3) = 'X';
  *(str + 4) = 'a';
  *(str + 5) = 0;

  // another example:
  // pattern_str = malloc(10 * 8);
  // *(pattern_str + 0) = 'f';
  // *(pattern_str + 1) = 'o';
  // *(pattern_str + 2) = 'o';
  // *(pattern_str + 3) = CHAR_BACKSLASH;
  // *(pattern_str + 4) = '.';
  // *(pattern_str + 5) = 't';
  // *(pattern_str + 6) = 'x';
  // *(pattern_str + 7) = 't';
  // *(pattern_str + 8) = 0;
  //
  // str = malloc(11 * 8);
  // *(str + 0) = 'f';
  // *(str + 1) = 'o';
  // *(str + 2) = 'o';
  // *(str + 3) = '.';
  // *(str + 4) = 't';
  // *(str + 5) = 'x';
  // *(str + 6) = 't';
  // *(str + 7) = 0;

  // res = 0 if matched; res = 1 if not matched
  res = fnmatch(pattern_str, str, 0);

  return 0;
}