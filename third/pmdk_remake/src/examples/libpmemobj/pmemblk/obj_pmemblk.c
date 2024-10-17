// SPDX-License-Identifier: BSD-3-Clause
/* Copyright 2015-2019, Intel Corporation */

/*
 * obj_pmemblk.c -- alternate pmemblk implementation based on pmemobj
 *
 * usage: obj_pmemblk [co] file blk_size [cmd[:blk_num[:data]]...]
 *
 *   c - create file
 *   o - open file
 *
 * The "cmd" arguments match the pmemblk functions:
 *   w - write to a block
 *   r - read a block
 *   z - zero a block
 *   n - write out number of available blocks
 *   e - put a block in error state
 */

#include <ex_common.h>
#include <sys/stat.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <errno.h>

#include "libpmemobj.h"
#include "libpmem.h"
#include "libpmemblk.h"

#define USABLE_SIZE (7.0 / 10)
#define POOL_SIZE ((size_t)(1024 * 1024 * 100))
#define MAX_POOL_SIZE ((size_t)1024 * 1024 * 1024 * 16)
#define MAX_THREADS 256
#define BSIZE_MAX ((size_t)(1024 * 1024 * 10))
#define ZERO_MASK (1 << 0)
#define ERROR_MASK (1 << 1)

POBJ_LAYOUT_BEGIN(obj_pmemblk);
POBJ_LAYOUT_ROOT(obj_pmemblk, struct base);
POBJ_LAYOUT_TOID(obj_pmemblk, uint8_t);
POBJ_LAYOUT_END(obj_pmemblk);

/* The root object struct holding all necessary data */
struct base {
	TOID(uint8_t) data;		/* contiguous memory region */
	TOID(uint8_t) flags;		/* block flags */
	size_t bsize;			/* block size */
	size_t nblocks;			/* number of available blocks */
	PMEMmutex locks[MAX_THREADS];	/* thread synchronization locks */
};

/*
 * pmemblk_map -- (internal) read or initialize the blk pool
 */
static int
pmemblk_map(PMEMobjpool *pop, size_t bsize, size_t fsize)
{
	int retval = 0;
	TOID(struct base) bp;
	bp = POBJ_ROOT(pop, struct base);

	/* read pool descriptor and validate user provided values */
	if (D_RO(bp)->bsize) {
		if (bsize && D_RO(bp)->bsize != bsize)
			return -1;
		else
			return 0;
	}

	/* new pool, calculate and store metadata */
	TX_BEGIN(pop) {
		TX_ADD(bp);
		D_RW(bp)->bsize = bsize;
		size_t pool_size = (size_t)(fsize * USABLE_SIZE);
		D_RW(bp)->nblocks = pool_size / bsize;
		D_RW(bp)->data = TX_ZALLOC(uint8_t, pool_size);
		D_RW(bp)->flags = TX_ZALLOC(uint8_t,
				sizeof(uint8_t) * D_RO(bp)->nblocks);
	} TX_ONABORT {
		retval = -1;
	} TX_END

	return retval;
}

/*
 * pmemblk_open -- open a block memory pool
 */
PMEMblkpool *
pmemblk_open(const char *path, size_t bsize)
{
	PMEMobjpool *pop = pmemobj_open(path, POBJ_LAYOUT_NAME(obj_pmemblk));
	if (pop == NULL)
		return NULL;
	struct stat buf;
	if (stat(path, &buf)) {
		perror("stat");
		return NULL;
	}

	return pmemblk_map(pop, bsize, buf.st_size) ? NULL : (PMEMblkpool *)pop;

}

/*
 * pmemblk_create -- create a block memory pool
 */
PMEMblkpool *
pmemblk_create(const char *path, size_t bsize, size_t poolsize, mode_t mode)
{
	/* max size of a single allocation is 16GB */
	if (poolsize > MAX_POOL_SIZE) {
		errno = EINVAL;
		return NULL;
	}

	PMEMobjpool *pop = pmemobj_create(path, POBJ_LAYOUT_NAME(obj_pmemblk),
				poolsize, mode);
	if (pop == NULL)
		return NULL;

	return pmemblk_map(pop, bsize, poolsize) ? NULL : (PMEMblkpool *)pop;
}

/*
 * pmemblk_close -- close a block memory pool
 */
void
pmemblk_close(PMEMblkpool *pbp)
{
	pmemobj_close((PMEMobjpool *)pbp);
}

/*
 * pmemblk_check -- block memory pool consistency check
 */
int
pmemblk_check(const char *path, size_t bsize)
{
	int ret = pmemobj_check(path, POBJ_LAYOUT_NAME(obj_pmemblk));
	if (ret)
		return ret;

	/* open just to validate block size */
	PMEMblkpool *pop = pmemblk_open(path, bsize);
	if (!pop)
		return -1;

	pmemblk_close(pop);
	return 0;
}

/*
 * pmemblk_set_error -- not available in this implementation
 */
int
pmemblk_set_error(PMEMblkpool *pbp, long long blockno)
{
	PMEMobjpool *pop = (PMEMobjpool *)pbp;
	TOID(struct base) bp;
	bp = POBJ_ROOT(pop, struct base);
	int retval = 0;

	if (blockno >= (long long)D_RO(bp)->nblocks)
		return 1;

	TX_BEGIN_PARAM(pop, TX_PARAM_MUTEX,
		&D_RW(bp)->locks[blockno % MAX_THREADS], TX_PARAM_NONE) {
		uint8_t *flags = D_RW(D_RW(bp)->flags) + blockno;
		/* add the modified flags to the undo log */
		pmemobj_tx_add_range_direct(flags, sizeof(*flags));
		*flags |= ERROR_MASK;
	} TX_ONABORT {
		retval = 1;
	} TX_END

	return retval;
}

/*
 * pmemblk_nblock -- return number of usable blocks in a block memory pool
 */
size_t
pmemblk_nblock(PMEMblkpool *pbp)
{
	PMEMobjpool *pop = (PMEMobjpool *)pbp;
	return ((struct base *)pmemobj_direct(pmemobj_root(pop,
					sizeof(struct base))))->nblocks;
}

/*
 * pmemblk_read -- read a block in a block memory pool
 */
int
pmemblk_read(PMEMblkpool *pbp, void *buf, long long blockno)
{
	PMEMobjpool *pop = (PMEMobjpool *)pbp;
	TOID(struct base) bp;
	bp = POBJ_ROOT(pop, struct base);

	if (blockno >= (long long)D_RO(bp)->nblocks)
		return 1;

	pmemobj_mutex_lock(pop, &D_RW(bp)->locks[blockno % MAX_THREADS]);

	/* check the error mask */
	uint8_t *flags = D_RW(D_RW(bp)->flags) + blockno;
	if ((*flags & ERROR_MASK) != 0) {
		pmemobj_mutex_unlock(pop,
				&D_RW(bp)->locks[blockno % MAX_THREADS]);
		errno = EIO;
		return 1;
	}

	/* the block is zeroed, reverse zeroing logic */
	if ((*flags & ZERO_MASK) == 0) {
		memset(buf, 0, D_RO(bp)->bsize);

	} else {
		size_t block_off = blockno * D_RO(bp)->bsize;
		uint8_t *src = D_RW(D_RW(bp)->data) + block_off;
		memcpy(buf, src, D_RO(bp)->bsize);
	}

	pmemobj_mutex_unlock(pop, &D_RW(bp)->locks[blockno % MAX_THREADS]);

	return 0;
}

/*
 * pmemblk_write -- write a block (atomically) in a block memory pool
 */
int
pmemblk_write(PMEMblkpool *pbp, const void *buf, long long blockno)
{
	PMEMobjpool *pop = (PMEMobjpool *)pbp;
	int retval = 0;
	TOID(struct base) bp;
	bp = POBJ_ROOT(pop, struct base);

	if (blockno >= (long long)D_RO(bp)->nblocks)
		return 1;

	TX_BEGIN_PARAM(pop, TX_PARAM_MUTEX,
		&D_RW(bp)->locks[blockno % MAX_THREADS], TX_PARAM_NONE) {
		size_t block_off = blockno * D_RO(bp)->bsize;
		uint8_t *dst = D_RW(D_RW(bp)->data) + block_off;
		/* add the modified block to the undo log */
		pmemobj_tx_add_range_direct(dst, D_RO(bp)->bsize);
		memcpy(dst, buf, D_RO(bp)->bsize);
		/* clear the error flag and set the zero flag */
		uint8_t *flags = D_RW(D_RW(bp)->flags) + blockno;
		/* add the modified flags to the undo log */
		pmemobj_tx_add_range_direct(flags, sizeof(*flags));
		*flags &= ~ERROR_MASK;
		/* use reverse logic for zero mask */
		*flags |= ZERO_MASK;
	} TX_ONABORT {
		retval = 1;
	} TX_END

	return retval;
}

/*
 * pmemblk_set_zero -- zero a block in a block memory pool
 */
int
pmemblk_set_zero(PMEMblkpool *pbp, long long blockno)
{
	PMEMobjpool *pop = (PMEMobjpool *)pbp;
	int retval = 0;
	TOID(struct base) bp;
	bp = POBJ_ROOT(pop, struct base);

	if (blockno >= (long long)D_RO(bp)->nblocks)
		return 1;

	TX_BEGIN_PARAM(pop, TX_PARAM_MUTEX,
		&D_RW(bp)->locks[blockno % MAX_THREADS], TX_PARAM_NONE) {
		uint8_t *flags = D_RW(D_RW(bp)->flags) + blockno;
		/* add the modified flags to the undo log */
		pmemobj_tx_add_range_direct(flags, sizeof(*flags));
		/* use reverse logic for zero mask */
		*flags &= ~ZERO_MASK;
	} TX_ONABORT {
		retval = 1;
	} TX_END

	return retval;
}

int
main(int argc, char *argv[])
{
	if (argc < 4) {
		fprintf(stderr, "usage: %s [co] file blk_size"\
			" [cmd[:blk_num[:data]]...]\n", argv[0]);
		return 1;
	}

	unsigned long bsize = strtoul(argv[3], NULL, 10);
	assert(bsize <= BSIZE_MAX);
	if (bsize == 0) {
		perror("blk_size cannot be 0");
		return 1;
	}

	PMEMblkpool *pbp;
	if (strncmp(argv[1], "c", 1) == 0) {
		pbp = pmemblk_create(argv[2], bsize, POOL_SIZE,
			CREATE_MODE_RW);
	} else if (strncmp(argv[1], "o", 1) == 0) {
		pbp = pmemblk_open(argv[2], bsize);
	} else {
		fprintf(stderr, "usage: %s [co] file blk_size"
			" [cmd[:blk_num[:data]]...]\n", argv[0]);
		return 1;
	}

	if (pbp == NULL) {
		perror("pmemblk_create/pmemblk_open");
		return 1;
	}

	/* process the command line arguments */
	for (int i = 4; i < argc; i++) {
		switch (*argv[i]) {
			case 'w': {
				printf("write: %s\n", argv[i] + 2);
				const char *block_str = strtok(argv[i] + 2,
							":");
				const char *data = strtok(NULL, ":");
				assert(block_str != NULL);
				assert(data != NULL);
				unsigned long block = strtoul(block_str,
							NULL, 10);
				if (pmemblk_write(pbp, data, block))
					perror("pmemblk_write failed");
				break;
			}
			case 'r': {
				printf("read: %s\n", argv[i] + 2);
				char *buf = (char *)malloc(bsize);
				assert(buf != NULL);
				const char *block_str = strtok(argv[i] + 2,
							":");
				assert(block_str != NULL);
				if (pmemblk_read(pbp, buf, strtoul(block_str,
						NULL, 10))) {
					perror("pmemblk_read failed");
					free(buf);
					break;
				}
				buf[bsize - 1] = '\0';
				printf("%s\n", buf);
				free(buf);
				break;
			}
			case 'z': {
				printf("zero: %s\n", argv[i] + 2);
				const char *block_str = strtok(argv[i] + 2,
							":");
				assert(block_str != NULL);
				if (pmemblk_set_zero(pbp, strtoul(block_str,
						NULL, 10)))
					perror("pmemblk_set_zero failed");
				break;
			}
			case 'e': {
				printf("error: %s\n", argv[i] + 2);
				const char *block_str = strtok(argv[i] + 2,
							":");
				assert(block_str != NULL);
				if (pmemblk_set_error(pbp, strtoul(block_str,
						NULL, 10)))
					perror("pmemblk_set_error failed");
				break;
			}
			case 'n': {
				printf("nblocks: ");
				printf("%zu\n", pmemblk_nblock(pbp));
				break;
			}
			default: {
				fprintf(stderr, "unrecognized command %s\n",
					argv[i]);
				break;
			}
		};
	}

	/* all done */
	pmemblk_close(pbp);

	return 0;
}
