/*
 * Copyright (C) 2017 C-SKY Microsystems Co., Ltd. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


void yunos_cpu_timer_init (void)
{
}


int yunos_user_cpu_time_get(void)
{
    return 0;
}


int yunos_user_sys_time_get(void)
{
    return 0;
}


#if (YUNOS_CONFIG_USER_HOOK > 0)

void yunos_init_hook(void)
{
#if (YUNOS_CONFIG_CPU_TIME > 0)
    yunos_cpu_timer_init();
#endif
}

void yunos_start_hook(void)
{

}

void yunos_task_create_hook(task_t *task)
{

}

void yunos_task_del_hook(task_t *task)
{

}

void yunos_task_abort_hook(task_t *task)
{

}

void yunos_idle_task_hook(void)
{

}

void yunos_task_switch_hook(void)
{

}

void yunos_tick_hook(void)
{

}

void yunos_idle_hook(void)
{

}

#endif


#if (YUNOS_CONFIG_INT_PRI_CHECK > 0)

void   yunos_intrpt_pri_check(void)
{


}

#endif

#if (YUNOS_CONFIG_ISR_STACK_FREE_GET > 0)

size_t yunos_user_isr_stack_free_get(void)
{

    return 0;
}

#endif

#if (YUNOS_CONFIG_ISR_STACK_CHECK > 0)

void yunos_intrpt_stack_check(void)
{


}

#endif
