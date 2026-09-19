# Why3 proves the imported response_inj law automatically.
# The header witness for page_after_blank remains explicit.
import Base
import ./main.bend as Srv
import ./LAWS.bend as Laws

def Laws.page_after_blank(page):
  ("HTTP/1.1 200 OK\r\nContent-Type: text/html\r\nConnection: close", {==})
