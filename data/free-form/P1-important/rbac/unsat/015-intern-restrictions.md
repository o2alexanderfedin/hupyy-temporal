# Intern File Access Restrictions

Mike is doing a summer internship at the company, working with the product team. He's been there about 6 weeks, still learning the ropes. His status in the system is intern, not a regular employee.

The company keeps sensitive stuff in /documents/confidential - things like financial reports, legal contracts, acquisition plans, employee salary data, that kind of thing. Pretty standard confidential business documents that not everyone should see.

The security policy is set up so that interns don't get access to confidential files. Makes sense since they're temporary and still getting up to speed. Regular employees have various levels of access depending on their role, but the intern role specifically excludes access to anything marked confidential.

Mike has the intern role assigned to his account. The intern role explicitly does not have permissions for confidential files. There's a document at /documents/confidential/q3-financial-projections.xlsx that Mike stumbled across while browsing the file system.

Mike wants to open the quarterly financial projections file. The file is located in the confidential directory. Interns don't have access to confidential materials.

Can Mike open the file at /documents/confidential/q3-financial-projections.xlsx?

Logic: QF_UFLIA
