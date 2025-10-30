# IT Admin Server Management

Jessica works in IT, been there about 5 years. She's got the IT administrator role, not just regular helpdesk support. She handles the infrastructure stuff, server management, that kind of thing.

The company has a bunch of production servers in the /servers directory of their management system. There's like /servers/web-prod, /servers/db-prod, /servers/api-gateway, all the critical stuff running the business.

Sometimes servers need to be restarted. Maybe there's a memory leak, maybe an update got applied, whatever the reason. It's a pretty sensitive operation since it can cause downtime if you're not careful.

The system is configured so that IT administrators have restart privileges for servers in the /servers directory. Regular employees definitely don't have this. Even most IT staff don't unless they have the full admin role.

Jessica has the IT administrator role assigned to her account. That admin role includes permissions to restart servers under /servers. One of the API servers at /servers/api-gateway has been acting weird and she thinks it needs a restart.

Can Jessica restart the server at /servers/api-gateway?

Logic: QF_UFLIA
