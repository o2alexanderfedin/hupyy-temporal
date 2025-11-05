# Product Warranty Verification

So this electronics company has a warranty policy posted on their website that says every single product they sell comes with at least a 1-year warranty. That's their public guarantee - ALL products, no exceptions, minimum 365 days warranty coverage.

Now we've got access to their product database with specific warranty information for the items they currently sell. Like:
- Product ID 101 (gaming laptop) has a 730-day warranty
- Product ID 102 (wireless mouse) has a 365-day warranty
- Product ID 103 (mechanical keyboard) has a 1095-day warranty
- Product ID 104 (USB-C hub) has a 548-day warranty
- Product ID 105 (monitor) has a 912-day warranty
- Product ID 106 (webcam) has a 365-day warranty
- Product ID 107 (headphones) has a 730-day warranty
- Product ID 108 (speaker system) has a 456-day warranty
- Product ID 109 (external SSD) has a 1460-day warranty
- Product ID 110 (charging cable) has a 365-day warranty

The universal policy claim is: for any product X in their catalog, the warranty duration for X is at least 365 days.

We know the specific warranty values for these 10 products we can see in the database. But there's that universal claim - does it actually hold for EVERY product they sell? Not just the ones we've listed here, but literally every item in their entire catalog including ones we haven't seen yet?

This gets interesting because we're checking a universal property (applies to all products, including ones not explicitly listed) against finite observations (specific products we know about). The relationship between "these specific examples all satisfy the policy" and "the universal policy holds for everything" is what makes this challenging.

Logic: UFLIA (with quantifiers)
