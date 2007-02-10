#!/usr/bin/python
""" SynGen - Server Side RSS Aggregator with MBOX output

Welcome to SynGen
-----------------

SynGen is short for Syndicator Generator, which is very confusing
because that's not what it does.  This is a tool designed to retreive
RSS feeds from web sites and store them in an MBOX style mailbox which
is suitable for reading via IMAP or your mail application of choice.

SynGen requires a feedlist.txt file as generated from the TRH Link
Manager.

SynGen is designed to be run via cron at regular intervals...1 hour
minimum recommended.

Requirements
------------

Python version 2.3 or greater.  See http://www.python.org/.

Installation
------------

Download syngen.py to a directory of your choice.

Download the latest feedparser from feedparser.org.

Configuration
-------------

Edit 'syngen.py' and set the directory paths and files as appropriate in
the 'User Configuration' section (see below).

Additionally, be sure to modify the first line to point to the correct
location of your Python interpreter (see above).

Execution
---------

For the initial run, it is recommended to run it by hand using the
following commands:

   # cd SynGen
   # ./syngen.py

Subsequent runs should be scheduled as a cron job.  The following entry
may be used to execute SynGen hourly:

   0 * * * * /path/to/SynGen/syngen.py

Additionally, periodic cleaning up of the cache is wise:

   30 1 * * * /path/to/SynGen/syngen.py -cleanup

Known Bugs
----------

None.

Unknown Bugs
------------

Probably several.
"""

__version__ = "1.4"
__date__ = "06/04/2004"
__author__ = "James E. Robinson, III  (james@robinsonhouse.com)"
__copyright__ = "Copyright 2004, James E. Robinson, III"
__license__ = "BSD"
__credits__ = ""
__contributors__ = ""

__history__ = """
1.5 - JER - 10/05/2004
   - add BlogLines API support

1.4 - JER - 06/04/2004
   - add enclosure support
   - use email.Message class for feederror code

1.3 - JER - 06/02/2004
   - updates for feedparser v.3.0-rc2
   - added unicode support, output now utf-8
   - use email.Message class to format messages
   - added NOUPDATE flag

1.2 - JER - 04/29/2004
   - fixed bug in firstNwords
   - variable changes
   - general clean-up

1.1 - JER - 01/07/2003
   - update for feedparser 2.7
   - re-worked guid, now you will not see modified posts

1.0 - JER - 12/30/2003
   - add support for dc:subject, if exists

0.9 - JER - 12/26/2003
   - reworked some logic to be more Python like
   - moved README and CHANGES file into source file

0.8 - JER - 12/01/2003 - Initial Python implementation
"""

"""
http://rpc.bloglines.com/update?user=user@example.com&ver=1
Response: |A|B|  a=unread count, b=unused

http://www.bloglines.com/export?id=jerobins
Response: OPML only

http://www.bloglines.com/public/jerobins
Response: browsable feed list

http://rpc.bloglines.com/blogroll?html=1&id=jerobins
Options:
html - 1,0
id - userid
folder - optional folder to display
Response: HTML feed list

http://rpc.bloglines.com/listsubs (BasicAuth)
Response: OPML with bloglines info

http://rpc.bloglines.com/getitems (BasicAuth)
Options:
s - subid, from listsubs above
n - mark read, vals=1,0
Response:
RSS 2.0 feed for subid
"""

import urllib2, base64, xml.sax

BLOGLINES = True
BLOGUSER = 'bloguser'
BLOGPASS = 'blogpass'

OPMLurl = 'http://rpc.bloglines.com/listsubs'
feedUrl = 'http://rpc.bloglines.com/getitems?n=0&s='
feedUrl = 'http://rpc.bloglines.com/getitems?n=1&s='

BasicAuth = base64.encodestring('%s:%s' % (BLOGUSER, BLOGPASS))[:-1]

# A SAX content handler that turns an OPML subscription list into a
# dictionary indexed by Bloglines subid

class OPMLHandler(xml.sax.ContentHandler):
   def startDocument(self):
      self.data = {}
      self.folder = ""
      
   def startElement(self,tag,attributes):
      if tag == 'outline':
         if attributes.has_key('xmlUrl'):
            if int(attributes['BloglinesUnread']) > 0:
               self.data[attributes['BloglinesSubId']] = self.folder
         else:
            self.folder = 'in_' + attributes['title'].lower()
         
def getBLdata(subid):

   url = feedUrl + subid
   req = urllib2.Request(url)
   req.add_header("Authorization", "Basic %s" % BasicAuth)

   f = urllib2.urlopen(req)
   xml = f.read()
   f.close()

   return xml

def getBLfeeds(xmlUrl):
   # Build parser      
   parser = xml.sax.make_parser()
   parser.setContentHandler(OPMLHandler())

   req = urllib2.Request(xmlUrl)
   req.add_header("Authorization", "Basic %s" % BasicAuth)

   f = urllib2.urlopen(req)

   BUFSIZE = 8192
   
   # feed the opml file to the parser a chunk at a time
   while True:
      data = f.read(BUFSIZE)
      if not data: break
      parser.feed(data)

   f.close()

   return parser._cont_handler.data

_DEBUG = 0
_NOUPDATE = 0

# system libraries
import sys, os, traceback
import md5, fcntl, string, time, cPickle, re, glob, sets
import email.Message, urllib, xml.sax.saxutils

# external libraries
try:
   import feedparser
except:
   print "Unable to import module FeedParser.  For download information"
   print "please see: http://sourceforge.net/projects/feedparser/"
   sys.exit(1)

HOME = os.environ.get('HOME')    # Users home directory

# User Configuration ---------------------------------------------------

VAR = HOME + "/var/syngen"       # storage location for RSS metadata
MAILDIR = HOME + "/mail/Offline" # directory to create/update mbox files

# location of file written by Link Manager
FEEDFILE = "/home/jerobins/public_html/docs/feedlist.txt" 

# End User Configuration -----------------------------------------------

# System Configuration -------------------------------------------------

MODIFIED = VAR + "/modified"
CACHE = VAR + "/cache"
RUNFILE = VAR + "/lastrun"

MAX_CACHE_ENTRIES = 200
MIN_CACHE_ENTRIES = 75

CURTIME = time.asctime(time.gmtime())

ENTITY_DICT = { '&apos;': "'", '&acirc;': "'", '&amp;': '&',
               '&quot;': '"', '&nbsp;': " ",
               '&rdquo;': '"', '&ldquo;': '"', 
               '&rsquo;': "'", '&lsquo;': "'" }

# security settings for file creation
os.umask(077)

# Set-up / First Run ---------------------------------------------------

def firstRunSetup():
   """
   args: none
   output: none
   returns: 0 - Success, 1 - Fail
   """

   try:
      os.mkdir(VAR)
      os.mkdir(MODIFIED)
      os.mkdir(CACHE)
   except:
      rc = 1
   else:
      try:
         fp = file(RUNFILE, "w")
      except:
         rc = 1
      else:
         fp.close()
         os.utime(RUNFILE, (00000000, 00000000))
         rc = 0

   return rc

def checkFirstRun():
   """
   args: none
   output: none
   returns: 0 - Success, 1 - Fail
   """

   if BLOGLINES: return

   try:
      fp = file(RUNFILE, 'r')
   except IOError:
      rc = firstRunSetup()
   else:
      fp.close()
      rc = 0

   return rc

# System Utilities -----------------------------------------------------

def _debuglog(message):
   if _DEBUG: print message
   return

def formatExceptionInfo(maxTBlevel=5):
   """
   args: maxTBlevel, default 5 - max levels for trackback information
   output: none
   returns: string with exception name, arguments and trackback info
   """

   cla, exc, trbk = sys.exc_info()
   excName = cla.__name__

   try:
      excArgs = exc.__dict__["args"]
   except KeyError:
      excArgs = "<no args>"

   excTb = traceback.format_tb(trbk, maxTBlevel)

   return excName + str(excArgs) + str(excTb)

# String Utilities -----------------------------------------------------

def stripHtmlTags(text):
   """
   args: text - string
   output: none
   returns: string with all tags removed
   """

   result = xml.sax.saxutils.unescape(text, ENTITY_DICT)
   zapTagsRe = re.compile('<.+?>')
   result = re.sub(zapTagsRe, '', result)
   return result

def stripNewlines(text):
   """
   args: text - string
   output: none
   returns: string with all newlines replaced with spaces
   """

   zapNewlinesRe = re.compile(r'(\n+|\r+)')
   result = re.sub(zapNewlinesRe, ' ', text)
   return result

def firstNwords(text, count=7):
   """
   args: text - string
         count - number of words max
   output: none
   returns: string with up to count words of the original text
   """

   expr = '(.+?\s+){1,%d}' % count
   fewWordsRe = re.compile(expr)
   few = fewWordsRe.search(text)
   if few != None:
      result = stripNewlines(few.group(0))
   else:
      result = text
   return result

# Mailbox Utilities ----------------------------------------------------

def writeMailbox(mbox, data):
   """
   args: mbox - filename
         data - text for output in MBOX format
   output: to file mbox
   returns: none / raise exception
   """

   fp = file(mbox, 'a')
   fd = fp.fileno()
   fcntl.lockf(fd, fcntl.LOCK_EX)
   fp.write(data)
   fcntl.lockf(fd, fcntl.LOCK_UN)
   fp.close()
   return

# Article Cache Utilities ----------------------------------------------

def saveArticleId(cfile, guid, truncate=0):
   """
   args: cfile - file and path of cache file
         guid - uniq hash of item data
         truncate - 0 no, 1 yes
   output: error string
   returns: none
   """

   if _NOUPDATE: return

   out = guid + "\n"

   if truncate:
      mode = 'w'
   else:
      mode = 'a'

   try:
      fp = file(cfile, mode)
      fp.write(out)
      fp.close()
   except:
      print "Error saving article id in file:", cfile

   return

def checkDupe(cfile, guid):
   """
   args: cfile - file and path of cache file
         guid - uniq hash of item data
   output: none
   returns: 1 - dupe, 0 - not dupe
   """

   try:
      fp = file(cfile, 'r')
   except:
      # file does not exist, make a new one
      saveArticleId(cfile, guid)
      dupe = 0
   else:
      data = fp.read()
      fp.close()

      data = string.split(data) # string to list

      dupe = data.count(guid)

      if not dupe:
         datlen = len(data)

         if datlen > MAX_CACHE_ENTRIES:
            goners = datlen - MIN_CACHE_ENTRIES
            del data[0:goners]

            data.append(guid)

            saveArticleId(cfile, string.join(data, '\n'), 1)
         else:
            saveArticleId(cfile, guid)

   return dupe

# Feed Cache Utilities -------------------------------------------------

def readMfile(mfile):
   """
   args: mfile - file and path to last modified data
   output: none
   returns: data dictionary with 'etag' and 'modified' values always set
   """

   data = { 'etag': None, 'modified': None }

   try:
      fp = file(mfile, 'r')
   except:
      pass
   else:
      try:
         cuke = cPickle.Unpickler(fp).load()
      except:
         pass
      else:
         data = cuke

      fp.close()
         
   return data

def writeMfile(mfile, data):
   """
   args: mfile - file and path to last modified data
         data - feedparser data dictionary
   output: none
   returns: 0 - Success, 1 - Fail
   """

   if _NOUPDATE: return 0

   data.setdefault('etag', None)
   data.setdefault('modified', None)

   output = {}
   output['etag'] = data['etag']
   output['modified'] = data['modified']

   try:
      fp = file(mfile, 'w')
   except:
      rc = 1
   else:
      cPickle.Pickler(fp).dump(output)
      fp.close()
      rc = 0

   return rc

# Cache File Utilities -------------------------------------------------

def cacheCleanup():
   """
   args: none
   output: text with count of files removed
   returns: none / raise exception
   """

   if BLOGLINES: return

   cnt = 0

   try:
      data = getFeedInfo()
   except:
      print "Unable to open FEEDFILE", FEEDFILE
      sys.exit(1)
   else:
      current = []
      for line in string.split(data):
         url, hash, mfile = string.split(line, '|')
         current.append(hash)
      
      os.chdir(CACHE)
      exists = glob.glob("*")

      curSet = sets.Set(current)
      existsSet = sets.Set(exists)
      extraSet = existsSet.difference(curSet)

      cnt = len(extraSet)

      for hash in extraSet:
         cfile = CACHE + "/" + hash
         mfile = MODIFIED + "/" + hash
         try:
            os.unlink(cfile)
            os.unlink(mfile)
         except:
            print "Unable to remove file:", hash
         else:
            continue

      print "SynGen: Removed %d cache files" % cnt

   return

# RSS Processing Functions ---------------------------------------------

def reportFeedError(detail, url, mbox):
   """
   args: detail - detail string of error
         url - RSS url 
         mbox - name of mailbox
   output: none
   returns: none / raise exception
   """

   validate = urllib.quote(url)
   detail = str(detail)

   msg = email.Message.Message()
   msg.set_unixfrom('From SynGen@SynGen.rss ' + CURTIME)
   msg.add_header('From', '"SynGen RSS Aggregator" <SynGen@SynGen.rss>')
   msg.add_header('To', '"RSS eMail Reader" <blogger@SynGen.rss>')
   msg.add_header('Subject', 'Error in RSS Feed')
   msg.add_header('Message-ID', '<' + url + '@feederror.syngen.rss>')
   msg.add_header('Date', CURTIME)
   msg.set_type('text/plain')
   msg.set_charset('iso-8859-1')
   msg.epilogue = ''
   payload = 'Problem parsing XML feed data.\n' + \
            'Feed URL: ' + url + '\n' + \
            'Error Detail: ' + detail + '\n' + \
            'Check with Feed Validator: ' + \
            'http://www.feedvalidator.org/check?url=' + validate + '\n'
   payload = payload.encode('iso-8859-1')
   msg.set_payload(payload, 'iso-8859-1')

   output = msg.as_string(True)
   output += '\n\n' # mbox seperator
   del msg

   writeMailbox(mbox, output)

   return

def rssToMbox(data, cfile = False):
   """
   args: data - feedparser data dictionary
         cfile - file and path to previously seen articles
   output: none
   returns: output string
   """

   output = []

   title = data['feed']['title']
   if not title:
      title = '(untitled)'

   title = stripNewlines(string.strip(title))
   title = xml.sax.saxutils.unescape(title, ENTITY_DICT)

   clink = data['feed']['link']

   # need the following: feed - title, clink
   #                     item - date, ititle, guid, ilink, desc
   for article in data['entries']:

      if article.has_key('modified_parsed'):
         date = time.asctime(article['modified_parsed'])
      else:
         date = CURTIME

      desc = ""

      if article.has_key('content'):
         clist = article['content']

         # stop if we get html content, continue otherwise
         for datum in clist:
            if datum['type'] == "text/html":
               desc = datum['value']
               break
            elif datum['type'] == "application/xhtml+xml":
               desc = datum['value']
               break
            else: # probably "text/plain"
               desc = datum['value']

      if not len(desc):
         if article.has_key('description'):
            desc = article['description']

      if not len(desc):
         desc = '(none provided)'

      ititle = ""

      if article.has_key('title'):
         ititle = stripHtmlTags(article['title'])

      if not len(ititle):
         ititle = firstNwords(stripHtmlTags(desc)) + "..."

      ititle = xml.sax.saxutils.unescape(ititle, ENTITY_DICT)
      ititle = string.strip(ititle)

      if article.has_key('link'):
         ilink = article['link']
      elif article.has_key('guid'):
         ilink = string.strip(article['guid'])
      else:
         ilink = clink

      if article.has_key('guid'):
         guid = string.strip(article['guid'])
      else:
         if isinstance(desc, unicode):
            guidText = desc.encode('ascii', 'ignore')
         else:
            try:
               guidText = str(desc)
            except UnicodeError:
               desc = unicode(desc, 'ascii', 'replace').encode('ascii')
               guidText = desc

         ml = md5.new(guidText)
         guid = ml.hexdigest()
         del ml
      
      if cfile:
         dupe = checkDupe(cfile, guid)
      else:
         dupe = False

      if article.has_key('enclosures'):
         enclosure = True
         fileURL = article['enclosures'][0]['url']
      else:
         enclosure = False

      if not dupe:
         msg = email.Message.Message()
         msg.set_unixfrom('From SynGen@SynGen.rss ' + date)
         msg.add_header('From', '"' + title + '" <SynGen@SynGen.rss>')
         msg.add_header('To', '"RSS eMail Reader" <blogger@SynGen.rss>')
         msg.add_header('Subject', ititle)
         msg.add_header('X-RSS-Link', ilink)
         if enclosure:
            msg.add_header('X-RSS-Enclosure', fileURL)
         msg.add_header('Message-ID', '<' + guid + '@' + clink + '>')
         msg.add_header('Date', date)
         msg.set_type('text/html')
         msg.set_charset('utf-8')
         msg.epilogue = ''
         payload = u'<h4><a href="' + ilink + u'">'
         payload += ititle + u'</a></h4>\n<p>\n'
         payload += desc + u'\n</p>\n'
         if enclosure:
            payload += u'<p>[<a href="' + fileURL + u'">Enclosure</a>]</p>'
         payload = payload.encode('utf-8')
         msg.set_payload(payload, 'utf-8')

         output.append(msg.as_string(True))
         output.append('\n\n') # mbox seperator
         del msg

   return string.join(output, "")

def processFeed(url, mbox, mfile = False, cfile = False):
   """
   args: url - RSS url 
         mfile - file and path to last modified data
         cfile - file and path to previously seen articles
         mbox - name of mailbox
   output: none
   returns: none / raise exception
   """

   if not BLOGLINES:
      data = readMfile(mfile)
      newdata = feedparser.parse(url, data['etag'], data['modified'])
   else:
      data = getBLdata(url)
      newdata = feedparser.parse(data)

   if len(newdata['items']):
      output = rssToMbox(newdata, cfile)

      if len(output) > 0:
         writeMailbox(mbox, output)
      
      writeMfile(mfile, newdata)
   elif newdata.has_key('status'):
      status = newdata['status']
      if status > 399:
         detail = "received HTTP error " + str(status)
         reportFeedError(detail, url, mbox)
   else:
      pass # let it go, could be xml error or not modified

   return

def getFeedInfo():
   """
   args: none
   output: none
   returns: data from feed file in raw format
   """

   fp = file(FEEDFILE, 'r')
   data = fp.read()
   fp.close()
   return data

def checkFeeds():
   """
   args: none
   output: error text on Fail
   returns: 0 - Success, > 0 - Fail
   """

   rc = 0

   if not BLOGLINES:
      try:
         data = getFeedInfo()

      except:
         print "Unable to open feedfile", FEEDFILE
         rc = 1
      else:
         for line in string.split(data):
            url, hash, mail = string.split(line, '|')

            cfile = CACHE + "/" + hash
            mfile = MODIFIED + "/" + hash
            mbox = MAILDIR + "/" + mail

            try:
               processFeed(url, mbox, mfile, cfile)
            except Exception, detail:
               detail = formatExceptionInfo()
               reportFeedError(detail, url, mbox)
   else:
      try:
         # feeds[key] = val, key = bloglinesSubId, val = mbox name
         feeds = getBLfeeds(OPMLurl)
      except:
         print "Unable to get BlogLines OPML subscriptions", OPMLurl
         rc = 1
      else:
         for subid in feeds.keys():
            mail = feeds[subid]
            mbox = MAILDIR + "/" + mail

            mfile = False
            cfile = False

            try:
               processFeed(subid, mbox)
            except Exception, detail:
               detail = formatExceptionInfo()
               reportFeedError(detail, subid, mbox)

   return rc

# ----------------------------------------------------------------------

def main():
   """
   args: uses sys.argv if exists
   output: useful status/error messages; hopefully
   returns: 0 - success, 1 - fail - uses sys.exit()
   """

   if len(sys.argv) > 1:
      if sys.argv[1] == "-cleanup":
         cacheCleanup()
   else:
      if checkFirstRun():
         print "Sorry, please verify configuration options and retry"
         sys.exit(1)

      if checkFeeds():
         print "Error processing feeds, aborting"
         sys.exit(1)
      else:
         os.utime(RUNFILE, None)

   sys.exit(0)

if __name__ == '__main__':
   main()
